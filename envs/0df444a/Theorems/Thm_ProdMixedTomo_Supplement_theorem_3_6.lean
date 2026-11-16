-- Prove2me | Theorems.Thm_ProdMixedTomo_Supplement_theorem_3_6
-- name    : ProdMixedTomo.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:33:21.963793+00:00
-- url     : https://prove2.me/theorems/858f98f4-5bdb-498c-a613-3ad4ee6f0000
-- title:
--   Theorem 3.6 — agnostic pure product state tomography from non-adaptive single-qubit measurements, error $O(\mathrm{opt}\sqrt{\log1/\mathrm{opt}})+\epsilon$
-- statement:
--   There are a universal constant $C>0$ and one program $L$ of the base measuring machine, which is non-adaptive (the measurement applied to each copy is fixed by the input $(n,N,\epsilon,\delta)$ alone), such that for every $n$, every $\epsilon,\delta>0$, every $n$-qubit density matrix $\rho$ and every
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=\frac{n\,\max\{1,\log(1/\delta)\}}{\epsilon^2},
--   $$
--   the following hold when $L$ is run on input $(n,N,\epsilon,\delta)$ with access to copies of $\rho$ only through single-copy, single-qubit measurements:
--   1. on every run, $L$ halts within $C(N+1)^C$ steps having measured at most $N$ copies;
--   2. with probability at least $1-\delta$, the output pure product state $|\hat\pi\rangle\in\Pi_n$ satisfies
--   $$
--   d_{\mathrm{tr}}\bigl(\rho,|\hat\pi\rangle\langle\hat\pi|\bigr)\ \le\ C\,\mathrm{opt}\sqrt{\max\{1,\log(1/\mathrm{opt})\}}+\epsilon,\qquad \mathrm{opt}=\mathrm{opt}(\Pi_n)=\inf_{|\pi\rangle\in\Pi_n}d_{\mathrm{tr}}(|\pi\rangle\langle\pi|,\rho),
--   $$
--   with the convention that the first term is $0$ when $\mathrm{opt}=0$.
--
--   Compared with the goal (Corollary 3.3), the hypothesis class is the pure product states, the copy complexity is linear in $n$, and no adaptivity is needed; the price is the larger error rate $\mathrm{opt}\sqrt{\log(1/\mathrm{opt})}$ measured against $\mathrm{opt}(\Pi_n)$.
--
--   Differences from the source:
--   - reading: "Let ϵ > 0, and let δ > 0. Let ρ be an n-qubit density matrix, There is an algorithm" → one program L and one constant C chosen before n, N, ϵ, δ and ρ; reason: the literal ∀ρ ∃ algorithm is trivial (hard-code a nearest pure product state); base reading R4
--   - reading: Õ(n log(1/δ)/ϵ²) → C·X·(log(2 + X))^C with X = n·max{1, log(1/δ)}/ϵ²; reason: polylog of the printed argument (stronger reading of Õ, base reading R2) and the log convention of p.13
--   - encoding: "an algorithm", "runs in poly(N) time", "given N copies" → an admissible program of the measuring real RAM halting within ⌊C·(N + 1)^C⌋ steps and consuming at most N copies on every run; reason: the paper names no machine (base reading R1)
--   - encoding: single-copy, single-qubit measurements → the machine's `measure` instruction: one fresh copy, each qubit measured projectively along a direction in ℝ³; reason: the base mission's access model; restricting the learner to projective single-qubit measurements only strengthens an existence claim
--   - reading: "non-adaptively chosen" measurements → NonAdaptive L: the direction tuple of the k-th measurement is the same along every execution path from the input, over all coin results and all outcomes; reason: the stronger reading (the choice may not depend on coins either); the paper's algorithm measures fixed X, Y, Z bases on fixed copies
--   - encoding: "a description of a pure product state |π̂⟩" → the halted state decoded by decodePure into ⊗ⱼ P(bⱼ) ∈ Π_n; reason: output layout of the base machine; P(0) := |0⟩⟨0| is the proof's "any unit vector"
--   - reading: O(opt √log(1/opt)) + ϵ → C·opt·√max{1, log(1/opt)} + ϵ, 0 at opt = 0; reason: the log convention of p.13 and the O-constant as the universal C
--   - encoding: "with probability at least 1 − δ" → run-law mass of {not halted, or error above the bound} at time ⌊C·(N + 1)^C⌋ is at most δ; reason: the base mission's run law
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6, p.19 (PDF p.21); proof and remark, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance
import Definitions.Def_ProdMixedTomo_Machine
import Definitions.Def_ProdMixedTomo_Supplement_PureProduct
import Definitions.Def_ProdMixedTomo_Supplement_gHalf
import Definitions.Def_ProdMixedTomo_Supplement_decodePure
import Definitions.Def_ProdMixedTomo_Supplement_NonAdaptive

namespace ProdMixedTomo.Supplement

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 3.6 (Agnostic Pure Product State Tomography), p.19 (PDF p.21). Let `ϵ, δ > 0` and
let `ρ` be an `n`-qubit density matrix. There is an algorithm, using only non-adaptively chosen,
single-copy, single-qubit measurements, which given `N ≥ N₀ = Õ(n log(1/δ)/ϵ²)` copies of `ρ`
runs in `poly(N)` time and outputs, with probability at least `1 − δ`, a description of a pure
product state `|π̂⟩` with `d_tr(ρ, |π̂⟩⟨π̂|) = O(opt √log(1/opt)) + ϵ`, where
`opt = opt(Π_n) = inf_{|π⟩ ∈ Π_n} d_tr(|π⟩⟨π|, ρ)`.

**Formalization Note.** One program `L` of the base measuring machine and one constant `C`, chosen
before `n, N, ϵ, δ, ρ` (as in `corollary_3_3`); `ρ` is reached only through `measure` (single
copy, single-qubit product measurement). `NonAdaptive L`: the direction tuple of the `k`-th
measurement is the same along every execution path from the input (all coin and outcome choices).
On every run `L` halts within `⌊C·(N + 1)^C⌋` steps having consumed at most `N` copies; the
output is decoded by `decodePure` into `Π_n`. `Õ(X) = C·X·(log(2+X))^C` with
`X = n·max{1, log(1/δ)}/ϵ²`; the error bound is `C·gHalf(opt(Π_n)) + ϵ`,
`gHalf(t) = t·√(max{1, log(1/t)})`. -/
theorem theorem_3_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ L : Program, Admissible L ∧ NonAdaptive L ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (ρ : QMat n), 0 < ϵ → 0 < δ → IsDensity ρ →
      otilde C ((n : ℝ) * logPlus (1 / δ) / ϵ ^ 2) ≤ N →
      (∀ s ∈ Reach L ρ (learnerInput n N ϵ δ) ⌊C * ((N : ℝ) + 1) ^ C⌋₊,
          s.halted = true ∧ s.copies ≤ N) ∧
      runLaw L ρ (learnerInput n N ϵ δ) ⌊C * ((N : ℝ) + 1) ^ C⌋₊
          {s | s.halted = false ∨ C * gHalf (optPure ρ) + ϵ < dtr ρ (decodePure n s)} ≤
        ENNReal.ofReal δ := by sorry

end ProdMixedTomo.Supplement
