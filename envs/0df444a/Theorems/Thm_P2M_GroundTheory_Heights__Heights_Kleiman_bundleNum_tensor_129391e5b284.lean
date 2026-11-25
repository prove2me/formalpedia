-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:44.917539+00:00
-- url     : https://prove2.me/theorems/fc81f2ef-228c-4dbd-ae4c-310ff17cc839
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bundle Num tensor 129391e5b284: P2 M Ground Theory Heights  Heights Kleiman bundle Num tensor 129391e5b284
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bundle Num tensor 129391e5b284 construction uses the P2 M Ground Theory Heights  Heights Kleiman bundle Num tensor 129391e5b284 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L137-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284 {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (Y Y' : LineBundle k x) :
    bundleNum pp (Function.update L i (Y.tensor Y')) =
      bundleNum pp (Function.update L i Y) + bundleNum pp (Function.update L i Y') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bundleNum_tensor» := P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tensor_129391e5b284
