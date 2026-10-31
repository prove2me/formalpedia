-- Prove2me | Theorems.Thm_SuperPareto_indep_isWNA
-- name    : SuperPareto.indep_isWNA
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:13.325239+00:00
-- url     : https://prove2.me/theorems/1fb4db87-b43c-4878-a2f8-fb0eb5bc87c4
-- title:
--   §2.1, p.5 — independent random variables are weakly negatively associated
-- statement:
--   Let $X_1,\dots,X_n$ be mutually independent real random variables on a probability space. Then $X_1,\dots,X_n$ are weakly negatively associated: for every $i$, every measurable decreasing set $S\subseteq\mathbb R^{n-1}$ and every $x\in\mathbb R$,
--
--   $$
--   P(\mathbf X_{-i}\in S,\ X_i\le x)\le P(\mathbf X_{-i}\in S)\,P(X_i\le x).
--   $$
--
--   This is the paper's remark that weak negative association "includes independence as a special case"; in particular the main theorem covers iid super-Pareto losses.
--
--   **Formalization Note** The index set is a finite type; mutual independence is Mathlib's `iIndepFun`.
--
--   Differences from the source:
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S, so these are the only sets for which (2) has a meaning
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.1, p.5, "Weak negative association includes independence as a special case."

import Mathlib
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Independence is a special case of weak negative association.** Chen, Embrechts, Wang,
*An unexpected stochastic dominance*, arXiv:2208.08471v4, §2.1, p.5, "Weak negative association
includes independence as a special case."

Mutually independent real random variables `X₁, …, Xₙ` on a probability space are weakly
negatively associated (`IsWNA`, Definition 2).

**Formalization Note.** The index set `[n]` is a `Fintype` `ι` (any size, `n = 1` included);
mutual independence is Mathlib's `iIndepFun`. -/
theorem indep_isWNA {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) :
    IsWNA P X := by sorry

end SuperPareto
