-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_proof_1_7_boundary
-- name    : SolomonRWRE.Recurrence.proof_1_7_boundary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:48.980661+00:00
-- url     : https://prove2.me/theorems/34be7f70-a382-4024-950b-c958559826ee
-- title:
--   §1, proof of Theorem (1.7), p. 5 — if α_n = 1 (α_n = 0) with positive probability but α_n > 0 (α_n < 1) for all n, case (i) (case (ii)) holds
-- statement:
--   Let $(X_n)$ be the random walk in the i.i.d. random environment $\alpha=(\alpha_n)_{n\in\mathbb Z}$, with $\sigma_n=(1-\alpha_n)/\alpha_n$ and $\rho_n=\sigma_1\cdots\sigma_n$.
--
--   1. If $P(\alpha_0=1)>0$ and $\alpha_n>0$ for all $n$, then case (i) of Theorem (1.7) holds:
--   $$\sum_{n=1}^\infty\frac1nP(\rho_n>1)<\infty\qquad\text{and}\qquad\lim_{n\to\infty}X_n=\infty\ \text{ almost surely.}$$
--   2. If $P(\alpha_0=0)>0$ and $\alpha_n<1$ for all $n$, then case (ii) holds:
--   $$\sum_{n=1}^\infty\frac1nP(\rho_n<1)<\infty\qquad\text{and}\qquad\lim_{n\to\infty}X_n=-\infty\ \text{ almost surely.}$$
--
--   These are the boundary cases of Theorem (1.7) in which $\sigma_n$ takes the value $0$ or $\infty$ with positive probability, which the paper treats separately from the case $0<\alpha_n<1$.
--
--   **Formalization Note** "Case (i) holds" is read as both the hypothesis and the conclusion of Theorem (1.7)(i). The nondegeneracy hypothesis is inherited from Theorem (1.7).
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 5, §1, proof of Theorem (1.7), first paragraph

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), §1, proof of
Theorem (1.7), p. 5, first paragraph: "If `α_n = 1`, (`α_n = 0`), with positive probability, but
`α_n > 0`, (`α_n < 1`), for all `n`, then it is clear that case (i), (case ii), holds."

**Formalization Note.** "Case (i) holds" is stated as both the hypothesis of Theorem (1.7)(i),
`Σ n⁻¹ P(ρ_n > 1) < ∞`, and its conclusion `X_n → ∞` a.e.; symmetrically for case (ii).
"With positive probability" is stated for `α_0` (the `α_n` are identically distributed), and
"for all `n`" for every outcome. The nondegeneracy hypothesis is inherited from
Theorem (1.7). -/
theorem proof_1_7_boundary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c) :
    ((0 < P {ω | α 0 ω = 1} ∧ ∀ n ω, 0 < α n ω) →
        seriesGt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    ((0 < P {ω | α 0 ω = 0} ∧ ∀ n ω, α n ω < 1) →
        seriesLt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) := by sorry

end SolomonRWRE.Recurrence
