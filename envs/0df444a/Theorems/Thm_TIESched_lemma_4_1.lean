-- Prove2me | Theorems.Thm_TIESched_lemma_4_1
-- name    : TIESched.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:41.763889+00:00
-- url     : https://prove2.me/theorems/9ce461e5-38e6-4988-8bd3-66ca7c2f2440
-- title:
--   Lemma 4.1 — a singleton instance violates the guarantee, or $F'(0)\ge\frac{m+1}2-\frac{m(m-1)\Gamma}{2H}$
-- statement:
--   Fix a star template ($L\ge1$, $H>1$, groups $J_0,\dots,J_{m-1}$) and a feasible fractional allocation family $x$, and let $\Gamma\in\mathbb R$. For an instance $I=(S,p)$ write $\mathrm{ALG}(I)=C(p,x^S(p))$. Then either some singleton instance $I=(\{j\},p^\sigma_{\{j\}})$ with $j\in J$ satisfies $\mathrm{ALG}(I)>\Gamma\,\mathrm{OPT}(I)$, or the expected center load satisfies
--   $$F'(0)\ \ge\ \frac{m+1}{2}-\frac{m(m-1)\Gamma}{2H}.$$
--
--   This compares the initial slope of the algorithm's center load with the optimum's slope $m$ and is the first input to Lemma 3.2.
--
--   Differences from the source:
--   - generalization: 0 ≤ Γ < (m+1)/2 and x of interaction order at most m − 1 (fixed on p.12) → every real Γ and every feasible x; reason: the proof (pp.13–14) uses only feasibility and the singleton guarantee; the Lean statement specializes to the source's
--   - encoding: F′(0) of the expectation F(ρ) → deriv at 0 of the explicit finite sum F; reason: F is that polynomial; same value
--   - encoding: vertices v_0, …, v_{m−1} and a bijection σ onto [m] → vertices Fin m with center 0 and σ : Equiv.Perm (Fin m); group labels are any pairwise disjoint sets of L natural numbers; reason: the same bijections and the same templates
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 4.1, p.13

import Mathlib
import Definitions.Def_TIESched_StarTemplate

set_option autoImplicit false

namespace TIESched

/-- **Lemma 4.1** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 4.1, p.13). For the star template
(`L ≥ 1`, `H > 1`) and a feasible fractional allocation family `x`: either a singleton instance
`I = ({j}, p^σ_{{j}})`, `j ∈ J`, satisfies `ALG(I) > Γ · OPT(I)`, or the expected center load satisfies
`F′(0) ≥ (m + 1)/2 − m(m − 1)Γ/(2H)`.

**Formalization Note.** `ALG(I)` is the makespan of `x` on the instance, `OPT` the optimal integral
makespan, `F′(0)` is `deriv F 0` of the explicit polynomial `F` (`StarTemplate.F`). The statement is
for every real `Γ` and every feasible `x` (no interaction-order assumption): the paper's standing
`0 ≤ Γ < (m+1)/2` and interaction order of §4 are not used. -/
theorem lemma_4_1 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (T : StarTemplate m) (x : AllocFamily m)
    (hx : Feasible x) (Γ : ℝ) :
    (∃ (σ : Equiv.Perm (Fin m)) (j : ℕ), j ∈ T.jobs ∧
        Γ * OPT (T.report σ {j}) < makespan (T.report σ {j}) (x {j} (T.report σ {j}))) ∨
      ((m : ℝ) + 1) / 2 - (m : ℝ) * ((m : ℝ) - 1) * Γ / (2 * T.H) ≤ deriv (T.F x) 0 := by sorry

end TIESched
