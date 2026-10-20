-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_separable_effects_normalization_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.separable_effects_normalization_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:31:32.123461+00:00
-- url     : https://prove2.me/theorems/deac5977-3b53-4da3-80a2-2338d3d4a346
-- title:
--   Separable deterministic effects suffice for the dual reduction
-- statement:
--   Let $\mathcal T$ be an operational probabilistic theory with systems, a trivial system $I$, sequential and parallel composition, identities, allowed tests, and coarse-graining. Physical events belong to allowed tests; deterministic events are singleton tests. States are events from $I$, effects are events to $I$, and $\mathrm{St}_+(A)$ is the finite conical hull of states of $A$. Let $F\in\mathrm{Transf}_{\mathbb R}(A,B)$ be a candidate in the real span of events, with its ambient ancillary action. No finite-dimensionality, local tomography, or physicality of $F$ is assumed. Write $L(F)$ for $(u|F|\rho)\leq1$ for every deterministic state $\rho$ of $A$ and every deterministic effect $u$ of $B$. Write $C(F)$ for $(u|F\otimes I_S|\Sigma)\leq1$ for every system $S$, every deterministic state $\Sigma$ of $AS$, and every deterministic effect $u$ of $BS$. Assume every deterministic bipartite effect of the theory is a finite convex combination $u=\sum_{j=1}^n p_j u_{j,B}\otimes u_{j,S}$ of product deterministic effects, with $p_j\geq0$ and $\sum_jp_j=1$. Then
--
--   $$C(F)\quad\Longleftrightarrow\quad L(F).$$
--
--   This is the dual reduction to the separable-state result. It requires neither causality nor positivity of $F$, and retains all deterministic effects rather than choosing one discard operation.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 26, Appendix F.2 final paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

section OperationalDefinitions

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℝ C]

variable [MonoidalCategory C] [SymmetricCategory C]

variable [MonoidalPreadditive C] [MonoidalLinear ℝ C]

/-- PDF p.26: dual separable deterministic-effect reduction; every deterministic
output effect remains quantified in both inequalities. -/
theorem separable_effects_normalization_iff (T : OperationalTheory C)
    (hT : HasSeparableDeterministicEffects T) {A B : C} (f : A ⟶ B) :
    CompleteUpperBound T f ↔ SingleUpperBound T f := by sorry

end OperationalDefinitions

end QAlgorithms.Papers.Independent.Dependency50.P06

end
