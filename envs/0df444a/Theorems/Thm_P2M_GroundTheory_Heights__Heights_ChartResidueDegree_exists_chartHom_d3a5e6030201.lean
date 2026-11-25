-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201
-- name    : P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:09.124872+00:00
-- url     : https://prove2.me/theorems/f19d7d8a-dd69-5a8e-8ad8-73fc622fb3bf
-- title:
--   P2 M Ground Theory Heights  Heights Chart Residue Degree exists chart Hom d3a5e6030201: P2 M Ground Theory Heights  Heights Chart Residue Degree exists chart Hom d3a5e6030201
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Residue Degree exists chart Hom d3a5e6030201 construction uses the P2 M Ground Theory Heights  Heights Chart Residue Degree exists chart Hom d3a5e6030201 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L29-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L29-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree

theorem P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201 {F : Type} [Field F] {n e : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)} [W.IsPrime]
    (hWh : IsHomogIdeal W) (hIW : I ≤ W) {t : Fin n → F}
    (ξ : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W))
    (hξ : ∀ h, aeval ξ h = algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ W)) (Ideal.Quotient.mk W h))
    (ℓ : FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hℓdef : ℓ = aeval ξ (linForm t)) (hℓ : ℓ ≠ 0)
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hc : ∑ j, c j * ξ j = 1) :
    ∃ ΦI : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)),
      (∀ s, ΦI (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) s) = aeval (genSubst ξ c) s) ∧
      (∀ h, ΦI (chartX I t e h) = C (aeval (fun m => ξ m / ℓ) h)) ∧
      ∀ h ∈ W, aeval (fun m => ξ m / ℓ) h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartResidueDegree».«exists_chartHom» := P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201
