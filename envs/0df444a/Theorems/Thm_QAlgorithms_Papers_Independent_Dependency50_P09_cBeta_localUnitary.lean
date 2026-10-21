-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_localUnitary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_localUnitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:54:36.301975+00:00
-- url     : https://prove2.me/theorems/b43522a6-3fdf-4bd5-abe9-4e3a5bfe74b2
-- title:
--   Corollary 8 (Invariance under local unitary channels)
-- statement:
--   Let $M:AB\to A'B'$ be CP and $U,V,W,Y$ be local unitaries on their respective ports. Write $\mathcal U,\mathcal V,\mathcal W,\mathcal Y$ for conjugation by these matrices.
--
--   $$
--   C_\beta((\mathcal W\otimes\mathcal Y)\circ M\circ(\mathcal U\otimes\mathcal V))=C_\beta(M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Uses the dimensionally matching systems in (134); the prose subscript on F is a relabeling typo.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 8, Corollary 8 (Invariance under local unitary channels)

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

/-- Corollary 8 (Invariance under local unitary channels), arXiv:2010.01058v3, PDF pp.8.
Uses the dimensionally matching systems in (134); the prose subscript on F is a relabeling typo.
Source correction: Printed: The prose gives F inconsistent input/output labels. Changed: Use the matching ports in equation (134). Why: Equation (134) and the proof compose the matching local unitary channels. -/
theorem cBeta_localUnitary {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (M : Superop (A × B) (C × D)) (hM : CP M)
    (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup B ℂ)
    (W : Matrix.unitaryGroup C ℂ) (Y : Matrix.unitaryGroup D ℂ) :
    cBeta (tensorAction (unitaryChannel W) (unitaryChannel Y) ∘ M ∘
      tensorAction (unitaryChannel U) (unitaryChannel V)) = cBeta M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
