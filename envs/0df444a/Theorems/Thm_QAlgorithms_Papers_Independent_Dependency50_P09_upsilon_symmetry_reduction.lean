-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_upsilon_symmetry_reduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.upsilon_symmetry_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:05:48.589181+00:00
-- url     : https://prove2.me/theorems/ebc8ac5a-ba4b-47d8-98cb-72be6ff07344
-- title:
--   Proposition 27
-- statement:
--   Let $N$ be covariant with respect to finite-group unitary representations $U_A:G$, $V_B:H$, $W_{A'}:G\times H$, and $Y_{B'}:G\times H$ as in (304). Let $D$ satisfy (142)–(144). Let $\mathcal C$ consist of CP comparison maps with these same representations, and $\mathcal S$ of normalized pure $\psi_{RAB}$ whose $AB$ marginal equals its independent $G,H$ twirl. In the second equality additionally assume both input representations are one-designs; $\Phi$ purifies $\pi_A\otimes\pi_B$.
--
--   $$
--   \Upsilon_D(N)=\inf_{M\in\mathcal C:\,\beta(M)\le1}\sup_{\psi\in\mathcal S}D(N(\psi)\Vert M(\psi)),\qquad \Upsilon_D(N)=\inf_{M\in\mathcal C:\,\beta(M)\le1}D(N(\Phi)\Vert M(\Phi))\ \text{under both one-design assumptions}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 17, Proposition 27

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

/-- Proposition 27, arXiv:2010.01058v3, PDF pp.17.
 -/
theorem upsilon_symmetry_reduction {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (W : G × H → Matrix.unitaryGroup C ℂ) (Y : G × H → Matrix.unitaryGroup D ℂ)
    (hU : Representation U) (hV : Representation V)
    (hW : Representation W) (hY : Representation Y)
    (div : Divergence) (hdiv : LawfulD div)
    (N : Superop (A × B) (C × D)) (hN : IsChannel N)
    (hcov : BiCovariant U V W Y N) :
    upsilon div N = symmetricUpsilon div U V W Y N ∧
      (OneDesign U → OneDesign V → upsilon div N = choiUpsilon div U V W Y N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
