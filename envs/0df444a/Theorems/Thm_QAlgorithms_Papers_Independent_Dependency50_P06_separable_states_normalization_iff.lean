-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_separable_states_normalization_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.separable_states_normalization_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:30:56.575764+00:00
-- url     : https://prove2.me/theorems/959de18c-f65d-4d04-85ae-1c46083f09a9
-- title:
--   Separable deterministic states suffice for the normalization reduction
-- statement:
--   Let $\mathcal T$ be an operational probabilistic theory with systems, a trivial system $I$, sequential and parallel composition, identities, allowed tests, and coarse-graining. Physical events belong to allowed tests; deterministic events are singleton tests. States are events from $I$, effects are events to $I$, and $\mathrm{St}_+(A)$ is the finite conical hull of states of $A$. Let $F\in\mathrm{Transf}_{\mathbb R}(A,B)$ be a candidate in the real span of events, with its ambient ancillary action. No finite-dimensionality, local tomography, or physicality of $F$ is assumed. Write $L(F)$ for $(u|F|\rho)\leq1$ for every deterministic state $\rho$ of $A$ and every deterministic effect $u$ of $B$. Write $C(F)$ for $(u|F\otimes I_S|\Sigma)\leq1$ for every system $S$, every deterministic state $\Sigma$ of $AS$, and every deterministic effect $u$ of $BS$. Assume every deterministic bipartite state of the theory has a decomposition $\Sigma=\sum_{j=1}^n p_j\alpha_j\otimes\sigma_j$, where $p_j\geq0$, $\sum_jp_j=1$, and both factors are deterministic states of their systems. Then
--
--   $$C(F)\quad\Longleftrightarrow\quad L(F).$$
--
--   Causality and complete positivity of the candidate are unnecessary for this algebraic reduction. It isolates a second circumstance where ancillary normalization tests are redundant; it makes no sufficiency assertion for physicality.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 25, Appendix F.2 concluding remark, pp.25–26

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

/-- PDF pp.25–26: separable deterministic states suffice for the same reduction,
without causality or complete positivity of the candidate. -/
theorem separable_states_normalization_iff (T : OperationalTheory C)
    (hT : HasSeparableDeterministicStates T) {A B : C} (f : A ⟶ B) :
    CompleteUpperBound T f ↔ SingleUpperBound T f := by sorry

end OperationalDefinitions

end QAlgorithms.Papers.Independent.Dependency50.P06

end
