-- Prove2me | Theorems.Thm_RiskBargaining_theorem_1_commensurable
-- name    : RiskBargaining.theorem_1_commensurable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:31:37.484826+00:00
-- url     : https://prove2.me/theorems/bdab1a07-2c4c-45d5-886c-03bfe7b56868
-- title:
--   Appendix A.3, p.36 (corrected: commensurable part of Theorem 1) — Axioms 1–3 force (9) at commensurable values
-- statement:
--   Let $F$ be a bargaining solution satisfying PAR, SYM and STR, and let $(R,M,\mathcal A)$ be an admissible instance whose values are natural multiples of one real $c>0$. Then
--   $$
--   F_i(R,M,\mathcal A)=\frac{v_i}{\sum_{j=1}^n v_j}\cdot z(R,M,\mathcal A),\qquad i\in N.
--   $$
--   In particular this applies whenever all $v_i$ are rational. This is clause (c) of the corrected Theorem 1, and the part of the printed "only if" that holds with the printed axioms alone.
--
--   Differences from the source:
--   - correction: the rational case of (9) is claimed for every feasible instance, with z the max in (8) → stated on admissible instances, where the max in (8) exists; reason: the max can fail to exist on a feasible instance; see RiskBargaining.proposition_1_counterexample (Ω = {1,2,3} uniform, 𝒜_±, ρ = 1/20, M = (11, 11, 8), R_1 = R_2 = 1)
--   - generalization: v_i ∈ ℚ; p ≥ 1 → all v_i are natural multiples of one real c > 0; p = ∞ admitted; reason: every rational family is commensurable, with c the inverse of a common denominator
--   - reading: X, Y and p are not listed in an instance; a bargaining solution acts on instances → X, Y, p are fixed parameters; F is a family over all finite nonempty player types; reason: Definition 2 lists only (R, M, 𝒜), and Axiom 3 changes the player set
--   - encoding: M : 𝒳 × Ω → ℝ; N′ = N∖{i} ∪ {(i,k) | k = 1,…,ℓ} → M : X → Lp ℝ p μ; player type {j // j ≠ i} ⊕ Fin ℓ with ℓ : ℕ+; reason: the same instances and the same game
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, proof of Theorem 1, p.36

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_SYM
import Definitions.Def_RiskBargaining_STR
import Definitions.Def_RiskBargaining_nashRule
import Definitions.Def_RiskBargaining_Instance_Commensurable

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Clause (c) of the corrected Theorem 1: the axioms force (9) at commensurable values.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, proof of Theorem 1, p.36.

A bargaining solution satisfying Axioms 1–3 equals rule (9) at every admissible instance whose values are
natural multiples of one positive real, in particular whenever all `v_i` are rational.

**Formalization Note.** The page treats `v_i ∈ ℚ`. Commensurability generalizes that, and the natural
multipliers are positive because `v_i > 0`. -/
theorem theorem_1_commensurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (F : Rule μ p X) (hF : IsBargainingSolution F) (hPAR : PAR F) (hSYM : SYM F) (hSTR : STR F)
    (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι)
    (hI : I.Admissible) (hc : I.Commensurable) :
    F ι I = nashRule ι I := by sorry

end RiskBargaining
