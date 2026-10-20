-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_beta_point_map_form
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.beta_point_map_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:21:42.953223+00:00
-- url     : https://prove2.me/theorems/8f68d523-6d2b-4acd-958d-dded206d5a3a
-- title:
--   Appendix A unnumbered point-to-point map-form beta (365)–(368)
-- statement:
--   Let $M:A\to B'$ be CP. Let $S\ge0$ be an arbitrary output operator, and $V:A\to B'$ a complex-linear Hermiticity-preserving map. Put $R^S(X)=\operatorname{Tr}(X)S$. The partial transpose in this point-channel case is the full transpose on the output; inequalities between maps mean complete positivity.
--
--   $$
--   \beta(M)=\inf\{\operatorname{Tr}S:\ T_{B\prime}\circ(V\pm M)\ \mathrm{CP},\ R^S\pm V\ \mathrm{CP}\}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The display alternates N and M; use M consistently with all constraints and Definition 1. No trace-one or trace-decreasing constraint is imposed on S.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 24, Appendix A unnumbered point-to-point map-form beta (365)–(368)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Appendix A unnumbered point-to-point map-form beta (365)–(368), arXiv:2010.01058v3, PDF pp.24.
The display alternates N and M; use M consistently with all constraints and Definition 1. No trace-one or trace-decreasing constraint is imposed on S.
Source correction: Printed: (365)-(368) alternate N in the objective with M in every constraint. Changed: Use the same arbitrary CP map M throughout. Why: Definition 1, (363)-(364) and Proposition 17 establish the CP-map program being specialized. -/
theorem beta_point_map_form {A : Type} [Fintype A] [Nonempty A]
    {D : Type} [Fintype D] [Nonempty D]
    (M : Superop A D) (hM : CP M) :
    bipartiteBeta (pointMap M) = pointBetaMap M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
