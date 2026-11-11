-- Prove2me | Theorems.Thm_ProdMixedTomo_theorem_4_5
-- name    : ProdMixedTomo.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:18.617113+00:00
-- url     : https://prove2.me/theorems/daea6624-8de8-42f5-9e3e-b5ec330b907a
-- title:
--   Theorem 4.5 — polynomial-time robust learner for binary products with error $O(\epsilon\log1/\epsilon)$
-- statement:
--   There are universal constants $\epsilon_0,C>0$ and one classical program $P$ such that for every $n$, every $0<\epsilon\le\epsilon_0$, every $\delta>0$, every mean $\nu\in[0,1]^n$, every $\epsilon$-corruption adversary $\mathrm{Adv}$, and every
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=\frac{n^2\max\{1,\log(1/\delta)\}}{\epsilon^2},
--   $$
--   the following hold when $P$ is run on input $(n,N,\epsilon,\delta)$ and the corrupted list $\mathrm{Adv}(S_g)$, $S_g\sim\mathrm{Bern}(\nu)^N$:
--   1. on every input of size $N$ and every run, $P$ halts within $C(N+1)^C$ steps;
--   2. except with probability $\delta$, the output mean vector $\hat\nu$ (clipped to $[0,1]^n$) satisfies
--   $$
--   d_{\mathrm{tv}}\bigl(\mathrm{Bern}(\nu),\mathrm{Bern}(\hat\nu)\bigr)\ \le\ C\,\epsilon\,\max\{1,\log(1/\epsilon)\}.
--   $$
--   This is the paper's second algorithmic contribution in its known-$\epsilon$ form; Theorem 1.8 follows from it.
--
--   Differences from the source:
--   - reading: "outputs with probability 0.99" with N₀ = Õ(n² log(1/δ)/ϵ²) → failure probability ≤ δ for every input δ > 0; reason: δ appears only in N₀; p.23 says boosting reduces to constant δ, so the statement with 1 − δ is the one the N₀ is for (reading R5); it implies the 0.99 form at δ = 0.01
--   - reading: "There is an algorithm (Algorithm 2)" → there is a program; reason: Algorithm 2 calls Lemma 4.8 (GLS ellipsoid), which is not itself a program of the machine; the theorem asserts an algorithm with this guarantee
--   - reading: Õ(n² log(1/δ)/ϵ²) → C·X·(log(2 + X))^C with X = n²·max{1, log(1/δ)}/ϵ²; reason: polylog of the printed argument (the stronger reading of Õ; the proofs give it)
--   - encoding: "an algorithm", "runs in poly(N) time" → an admissible program of the measuring real RAM (Def_ProdMixedTomo_Machine) halting within ⌊C·(N + 1)^C⌋ steps on every run; reason: the paper names no machine (unit-cost real RAM, rational literals, no √, floor or eigensolver); N + 1 because every run needs a step and N may be 0
--   - encoding: ϵ-corrupted set of samples (Definition 2.1) → an ϵ-corruption adversary applied to N i.i.d. clean samples; failure probability Σ over clean lists of Bern(ν)^N weight times the run law; reason: the adversary sees the clean sample, not the coins (Def_ProdMixedTomo_Corruption)
--   - encoding: "outputs … the mean vector for a product distribution p̂" → output vector in memory, clipped to [0,1]ⁿ, read as Bern(·); reason: a mean vector of a product distribution lies in [0,1]ⁿ
--   - reading: d_tv(p, p̂) ≲ ϵ log 1/ϵ → ≤ C·g(ϵ) = C·ϵ·max{1, log(1/ϵ)}; reason: ≲ and the log convention, p.13
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 4.5, p.22 (PDF p.24); Algorithm 2 and proof, pp.29–30 (PDF pp.31–32)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Machine
import Definitions.Def_ProdMixedTomo_Corruption

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 4.5, p.22 (PDF p.24). There is a universal `ϵ₀ > 0` and an algorithm which, given
`ϵ ≤ ϵ₀` and an `ϵ`-corrupted set of `N ≥ N₀ = Õ(n² log(1/δ)/ϵ²)` samples from an unknown
product distribution `p ∈ P_n`, outputs the mean vector of a product distribution `p̂` with
`d_tv(p, p̂) ≲ ϵ log 1/ϵ`, except with probability `δ`, and runs in time `poly(N)`.

**Formalization Note.** Reading: the printed "with probability 0.99" next to an `N₀` that
depends on `δ` is read as success probability `1 − δ` (stronger; the paper's p.23 reduces to
constant `δ` by boosting). The algorithm is a classical program of the machine
(`Definitions.Def_ProdMixedTomo_Machine`) with input `(n, N, ϵ, δ, samples)`; "(Algorithm 2)" is
read existentially. The adversary sees the clean samples, not the coins. `poly(N)` is
`C·(N + 1)^C` steps on every input and run; the output mean is clipped to `[0,1]ⁿ`. -/
theorem theorem_4_5 :
    ∃ ϵ₀ C : ℝ, 0 < ϵ₀ ∧ 0 < C ∧ ∃ P : Program, Admissible P ∧ IsClassical P ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (ν : Fin n → ℝ) (Adv : (Fin N → Cube n) → (Fin N → Cube n)),
      0 < ϵ → ϵ ≤ ϵ₀ → 0 < δ → ν ∈ MeanBox n → IsCorruption ϵ Adv →
      otilde C ((n : ℝ) ^ 2 * logPlus (1 / δ) / ϵ ^ 2) ≤ N →
      (∀ S : Fin N → Cube n, ∀ s ∈ cReach P (classicalInput n N ϵ δ S)
          ⌊C * ((N : ℝ) + 1) ^ C⌋₊, s.halted = true) ∧
      ∑ S : Fin N → Cube n, ENNReal.ofReal (∏ i, bern ν (S i)) *
        cRunLaw P (classicalInput n N ϵ δ (Adv S)) ⌊C * ((N : ℝ) + 1) ^ C⌋₊
          {s | s.halted = false ∨ C * gErr ϵ < dtv (bern ν) (outBern n s)} ≤
        ENNReal.ofReal δ := by sorry

end ProdMixedTomo
