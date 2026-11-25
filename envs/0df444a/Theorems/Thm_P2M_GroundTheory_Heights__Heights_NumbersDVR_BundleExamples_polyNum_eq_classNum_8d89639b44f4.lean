-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:39.446942+00:00
-- url     : https://prove2.me/theorems/b5bc4612-7c75-48dc-bc60-6cb32a6a3959
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples poly Num eq class Num 8d89639b44f4: P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples poly Num eq class Num 8d89639b44f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples poly Num eq class Num 8d89639b44f4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Bundle Examples poly Num eq class Num 8d89639b44f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L124-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ClassListMapDomainPerm.lean#L124-L145

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4 {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m : ℕ} (deg : Fin m → K → ℤ) {τ : Type*} [DecidableEq τ] (e : Fin m ≃ τ) (cls : τ → K → ℤ)
    (hcls : cls ∘ e = deg) {H : MvPolynomial (Fin m) ℤ} {d : ℕ} (hH : H.IsHomogeneous d)
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ L => intNum (IsLocalRing.ResidueField O) V L)
                              (specialIdeal W) d deg H = classNum cls (rename e H) [] W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BundleExamples».«polyNum_eq_classNum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_polyNum_eq_classNum_8d89639b44f4
