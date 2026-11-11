-- Prove2me | Theorems.Thm_ProdMixedTomo_theorem_3_1
-- name    : ProdMixedTomo.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:36.142856+00:00
-- url     : https://prove2.me/theorems/dd70f41a-a9a3-4521-aec9-61965708890e
-- title:
--   Theorem 3.1 — black-box reduction from agnostic product-state tomography to robust binary-product learning (corrected: $n+1$ in the time bound)
-- statement:
--   Fix $n$, sample sizes $N_{\mathrm{mean}},N_{\mathrm{density}}$, time bounds $T_{\mathrm{mean}},T_{\mathrm{density}}$, an accuracy parameter $\xi>0$, a failure parameter $\delta$, and error functions $f_{\mathrm{mean}},f_{\mathrm{density}}$. Suppose $A_{\mathrm{mean}}$ and $A_{\mathrm{density}}$ are classical programs such that:
--   1. on every input of $N_{\mathrm{mean}}$ (resp. $N_{\mathrm{density}}$) points of $\{0,1\}^n$, every run halts within $T_{\mathrm{mean}}$ (resp. $T_{\mathrm{density}}$) steps;
--   2. (Problem 2) for every $\epsilon$, every $\nu\in[0,1]^n$ and every distribution $q$ with $d_{\mathrm{tv}}(\mathrm{Bern}(\nu),q)\le\epsilon$, on $N_{\mathrm{mean}}$ i.i.d. samples from $q$ the output $\hat\mu$ satisfies $\|\hat\mu-\nu\|_2\le f_{\mathrm{mean}}(\epsilon)+\xi$ except with probability $\delta/6$;
--   3. (Problem 3) likewise, on $N_{\mathrm{density}}$ samples the output $\hat p\in\mathcal P_n$ satisfies $d_{\mathrm{tv}}(\hat p,\mathrm{Bern}(\nu))\le f_{\mathrm{density}}(\epsilon)+\xi$ except with probability $\delta/2$.
--
--   Then there is a learner which, for every $n$-qubit density matrix $\rho$, uses exactly $3N_{\mathrm{mean}}+N_{\mathrm{density}}$ single-copy single-qubit measurements, halts on every run within $C\bigl(3T_{\mathrm{mean}}+T_{\mathrm{density}}+(n+1)(N_{\mathrm{mean}}+N_{\mathrm{density}})\bigr)$ steps, and outputs $\hat\pi\in\mathcal M_n$ with
--   $$
--   d_{\mathrm{tr}}(\rho,\hat\pi)\ \le\ \mathrm{opt}+\sqrt6\,f_{\mathrm{mean}}(\mathrm{opt})+f_{\mathrm{density}}(\mathrm{opt})+(1+\sqrt6)\,\xi
--   $$
--   except with probability $\delta$, where $\mathrm{opt}=\inf_{\pi\in\mathcal M_n}d_{\mathrm{tr}}(\pi,\rho)$ and $C$ is a universal constant.
--
--   This is the paper's first half: agnostic tomography of product mixed states reduces, with no loss in copies or time, to robust learning of binary product distributions.
--
--   **Formalization Note** Programs, layouts and decoders are those of the machine definition; the subroutines receive $\xi$ and their failure probability as their two real inputs, the learner receives $\xi$ and $\delta$. The learner may depend on all the data above; $C$ may not.
--
--   Differences from the source:
--   - correction: runs in time O(3T_mean + T_density + n(N_mean + N_density)) → halts within ⌊C·(3T_mean + T_density + (n + 1)(N_mean + N_density))⌋ steps; reason: the printed bound is false at n = 0: with A_mean = A_density = [halt] (T_mean = T_density = 1, every hypothesis holds since the outputs are exact on the one-point cube) and N_mean = 10⁶, the learner must take 3·10⁶ measurements, each at least one step, within O(1) time; (n + 1) ≤ 2n for n ≥ 1, so nothing changes there
--   - reading: "achieves error f(opt) ≤ opt + √6 f_mean(opt) + f_density(opt)" for Problem 1's "+ ϵ" → opt + √6 f_mean(opt) + f_density(opt) + (1 + √6)ξ with ξ the subroutines' accuracy parameter; reason: the proof ends with "+ (√6 + 1)ϵ … up to adjusting constants in the ϵ" (p.19); the explicit form is that statement
--   - encoding: algorithms for Problems 2 and 3 with error rates, sample complexities, failure probabilities δ/6, δ/2 and running times → admissible classical programs with the stated specification at every contamination level ϵ, on fixed sample sizes, halting within T on every input and run; reason: Problems 2–3 (p.14) as specifications of programs of the mission's machine
--   - encoding: "uses 3N_mean + N_density single-copy single-qubit measurements" → every run halts having executed exactly 3N_mean + N_density measure instructions; reason: measure is the machine's single-copy product single-qubit measurement
--   - encoding: "runs in time O(·)" → an admissible program of the measuring real RAM, the time counted in executed instructions on every run; reason: the paper names no machine (unit-cost real RAM, rational literals, no √, floor or eigensolver); N + 1 because every run needs a step and N may be 0
--   - encoding: O(·) / ≲ / Ω(·) → ∃ C > 0 chosen before n, the sample sizes, time bounds, ξ, δ, f_mean, f_density and the subroutines; reason: meaning of a universal constant (p.13)
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.1, p.15 (PDF p.17); Problems 2–3, p.14 (PDF p.16); Algorithm 1, p.15 (PDF p.17); proof, pp.17–19 (PDF pp.19–21)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Machine

open scoped ComplexOrder

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.1, p.15 (PDF p.17). Black-box reduction from agnostic tomography of product mixed
states (Problem 1) to robust mean estimation (Problem 2) and robust density estimation
(Problem 3) for binary product distributions.

Given classical programs `A_mean`, `A_density` that, on `N_mean` (resp. `N_density`) samples
`ϵ`-contaminated from any `Bern(ν)` (for every `ϵ`) and accuracy parameter `ξ > 0`, output
`μ̂` with `‖μ̂ − ν‖₂ ≤ f_mean(ϵ) + ξ` (resp. `p̂` with `d_tv(p̂, Bern ν) ≤ f_density(ϵ) + ξ`) except
with probability `δ/6` (resp. `δ/2`), and halt within `T_mean` (resp. `T_density`) steps on every
input and every run, there is a learner that uses exactly `3N_mean + N_density` single-copy
single-qubit measurements, halts within `C(3T_mean + T_density + (n + 1)(N_mean + N_density))`
steps on every run, and outputs `π̂ ∈ M_n` with
`d_tr(ρ, π̂) ≤ opt + √6 f_mean(opt) + f_density(opt) + (1 + √6)ξ` except with probability `δ`.

**Formalization Note.** The machine, layouts and decoders are those of
`Definitions.Def_ProdMixedTomo_Machine`; the subroutines receive `ξ` and their failure
probability in `M[0]`, `M[1]`; the learner receives `ξ` and `δ`. The paper's "+ϵ" of Problem 1 is
the explicit `(1 + √6)ξ` of the proof (p.19). `C` is universal, chosen before all data.
Correction: the printed time `O(3T_mean + T_density + n(N_mean + N_density))` is false at `n = 0`
(with `A_mean = A_density = [halt]`, `T_mean = T_density = 1`, `N_mean = 10⁶` the learner must take
`3·10⁶` measurements in `O(1)` steps); `n + 1` replaces `n`, which is the same bound up to the
constant for every `n ≥ 1`. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n Nm Nd Tm Td : ℕ) (ξ δ : ℝ) (fm fd : ℝ → ℝ) (Am Ad : Program),
      0 < ξ →
      Admissible Am → IsClassical Am → Admissible Ad → IsClassical Ad →
      (∀ S : Fin Nm → Cube n,
        ∀ s ∈ cReach Am (classicalInput n Nm ξ (δ / 6) S) Tm, s.halted = true) →
      (∀ S : Fin Nd → Cube n,
        ∀ s ∈ cReach Ad (classicalInput n Nd ξ (δ / 2) S) Td, s.halted = true) →
      (∀ (ϵ : ℝ) (ν : Fin n → ℝ) (q : Cube n → ℝ), ν ∈ MeanBox n → IsDist q →
        dtv (bern ν) q ≤ ϵ →
        sampleFail Am n Nm ξ (δ / 6) q Tm
          (fun s => fm ϵ + ξ < Real.sqrt (∑ j, (outVec n s j - ν j) ^ 2)) ≤
          ENNReal.ofReal (δ / 6)) →
      (∀ (ϵ : ℝ) (ν : Fin n → ℝ) (q : Cube n → ℝ), ν ∈ MeanBox n → IsDist q →
        dtv (bern ν) q ≤ ϵ →
        sampleFail Ad n Nd ξ (δ / 2) q Td
          (fun s => fd ϵ + ξ < dtv (outBern n s) (bern ν)) ≤ ENNReal.ofReal (δ / 2)) →
      ∃ L : Program, Admissible L ∧
        ∀ ρ : QMat n, IsDensity ρ →
          (∀ s ∈ Reach L ρ (learnerInput n (3 * Nm + Nd) ξ δ)
              ⌊C * (((3 * Tm + Td : ℕ) : ℝ) + ((n : ℝ) + 1) * ((Nm + Nd : ℕ) : ℝ))⌋₊,
            s.halted = true ∧ s.copies = 3 * Nm + Nd) ∧
          runLaw L ρ (learnerInput n (3 * Nm + Nd) ξ δ)
              ⌊C * (((3 * Tm + Td : ℕ) : ℝ) + ((n : ℝ) + 1) * ((Nm + Nd : ℕ) : ℝ))⌋₊
            {s | s.halted = false ∨
              optM ρ + Real.sqrt 6 * fm (optM ρ) + fd (optM ρ) + (1 + Real.sqrt 6) * ξ <
                dtr ρ (decodeState n s)} ≤ ENNReal.ofReal δ := by sorry

end ProdMixedTomo
