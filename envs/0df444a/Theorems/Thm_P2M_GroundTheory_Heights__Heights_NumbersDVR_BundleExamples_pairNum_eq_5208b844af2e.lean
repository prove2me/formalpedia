-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_pairNum_eq_5208b844af2e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_pairNum_eq_5208b844af2e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:53.169367+00:00
-- url     : https://prove2.me/theorems/53cd346c-e85c-488b-a194-a2ce76e93cb8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples pair Num eq 5208b844af2e: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples pair Num eq 5208b844af2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples pair Num eq 5208b844af2e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples pair Num eq 5208b844af2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L201-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L201-L218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_pairNum_eq_5208b844af2e {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (P : Ideal (MRing ι O)) (d : ℕ) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    {G : MvPolynomial (Fin r) ℤ} (hG : G.IsHomogeneous (d + 1)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
                              y y' f g G =
      pairNum P y y' f g
        (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G)) [] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«pairNum_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_pairNum_eq_5208b844af2e
