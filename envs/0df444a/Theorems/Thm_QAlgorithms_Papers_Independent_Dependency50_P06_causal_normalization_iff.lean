-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_causal_normalization_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.causal_normalization_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:27:35.266512+00:00
-- url     : https://prove2.me/theorems/f16bc9bc-2cb4-42dc-af77-68f0cbd50138
-- title:
--   Causality reduces ancillary normalization to single systems
-- statement:
--   Let $\mathcal T$ be an operational probabilistic theory with systems, a trivial system $I$, sequential and parallel composition, identities, allowed tests, and coarse-graining. Physical events belong to allowed tests; deterministic events are singleton tests. States are events from $I$, effects are events to $I$, and $\mathrm{St}_+(A)$ is the finite conical hull of states of $A$. Let $F\in\mathrm{Transf}_{\mathbb R}(A,B)$ be a candidate in the real span of events, with its ambient ancillary action. No finite-dimensionality, local tomography, or physicality of $F$ is assumed. Write $L(F)$ for $(u|F|\rho)\leq1$ for every deterministic state $\rho$ of $A$ and every deterministic effect $u$ of $B$. Write $C(F)$ for $(u|F\otimes I_S|\Sigma)\leq1$ for every system $S$, every deterministic state $\Sigma$ of $AS$, and every deterministic effect $u$ of $BS$. Assume $\mathcal T$ is causal, equivalently each system has a unique deterministic effect. Then
--
--   $$C(F)\quad\Longleftrightarrow\quad L(F).$$
--
--   The output effects on $BS$ and on $B$ have their respective system types; the composite deterministic effect factorizes. This explains why a separate ancillary trace bound is redundant in causal theories.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 24, Proposition F.12

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

/-- PDF p.24, Proposition F.12: causality removes ancillary normalization tests,
for a candidate transformation without a positivity assumption. -/
theorem causal_normalization_iff (T : OperationalTheory C) (hT : IsCausal T)
    {A B : C} (f : A ⟶ B) :
    CompleteUpperBound T f ↔ SingleUpperBound T f := by sorry

end OperationalDefinitions

end QAlgorithms.Papers.Independent.Dependency50.P06

end
