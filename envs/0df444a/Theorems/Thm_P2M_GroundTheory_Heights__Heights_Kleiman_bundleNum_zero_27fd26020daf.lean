-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:34.550939+00:00
-- url     : https://prove2.me/theorems/930eb826-53f1-4d63-881b-9e2e68cddd3c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bundle Num zero 27fd26020daf: P2 M Ground Theory Heights  Heights Kleiman bundle Num zero 27fd26020daf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bundle Num zero 27fd26020daf construction uses the P2 M Ground Theory Heights  Heights Kleiman bundle Num zero 27fd26020daf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L145-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L145-L157

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) :
    bundleNum pp (Function.update L i (twistBundle k x 0)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bundleNum_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_zero_27fd26020daf
