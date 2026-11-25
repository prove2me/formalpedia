-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_update_tensor_82be194f3bfb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_update_tensor_82be194f3bfb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:54.259642+00:00
-- url     : https://prove2.me/theorems/1027da13-d667-556c-bbe1-51d4239300bf
-- title:
--   P2 M Ground Theory Heights  Heights Inter pts Integral update tensor 82be194f3bfb: P2 M Ground Theory Heights  Heights Inter pts Integral update tensor 82be194f3bfb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pts Integral update tensor 82be194f3bfb construction uses the P2 M Ground Theory Heights  Heights Inter pts Integral update tensor 82be194f3bfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeSlotAdd.lean#L34-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeSlotAdd.lean#L34-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeSlotAdd
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_update_tensor_82be194f3bfb (hE : ResExistsStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) {L : Fin e → HermLine ι} (j : Fin e) {M N A : HermLine ι}
    {s : MRing ι} (hL : ∀ i, IsSmoothHerm (L i)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot (Function.update L j (M.tensor N))) (logNorm A s) =
      ptsIntegral P (pot (Function.update L j M)) (logNorm A s) +
        ptsIntegral P (pot (Function.update L j N)) (logNorm A s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptsIntegral_update_tensor» := P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_update_tensor_82be194f3bfb
