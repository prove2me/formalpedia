-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_beta_map_form
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.beta_map_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:21:01.396813+00:00
-- url     : https://prove2.me/theorems/b655bb19-7c9c-483a-98a8-443d328502a1
-- title:
--   Appendix A unnumbered map-form beta equality (363)–(364)
-- statement:
--   Let $M:AB\to A'B'$ be CP on finite positive-dimensional ports. Optimize over complex-linear Hermiticity-preserving maps $S,V$ with $T_{B'}\circ(V\pm M)\circ T_B$ CP, $S\pm V$ CP, and $\operatorname{Tr}_{A'}\circ S=\operatorname{Tr}_{A'}\circ S\circ R_A^\pi$, where $R_A^\pi(X)=\pi_A\otimes\operatorname{Tr}_A X$. Both signs are required. Feasibility forces $S$ to be CP; its induced trace norm equals $\sup_{\rho\text{ density}}\operatorname{Tr}S(\rho)$.
--
--   $$
--   \beta(M)=\inf_{S,V\ \mathrm{feasible}}\|S\|_{1\to1}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Equality to the independent map optimization is a theorem, not an assumption. The objective is the induced trace norm on CP maps, not an entrywise or diamond norm.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 23, Appendix A unnumbered map-form beta equality (363)–(364)

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

/-- Appendix A unnumbered map-form beta equality (363)–(364), arXiv:2010.01058v3, PDF pp.23,24.
Equality to the independent map optimization is a theorem, not an assumption. The objective is the induced trace norm on CP maps, not an entrywise or diamond norm. -/
theorem beta_map_form {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (M : Superop (A × B) (C × D)) (hM : CP M) :
    bipartiteBeta M = betaMapValue M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
