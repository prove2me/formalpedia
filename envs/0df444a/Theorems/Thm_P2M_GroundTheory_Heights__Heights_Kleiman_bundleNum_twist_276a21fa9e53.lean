-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:02.632288+00:00
-- url     : https://prove2.me/theorems/9e95df4a-23c3-4fe8-a6c4-4ee195c5aa8c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bundle Num twist 276a21fa9e53: P2 M Ground Theory Heights  Heights Kleiman bundle Num twist 276a21fa9e53
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bundle Num twist 276a21fa9e53 construction uses the P2 M Ground Theory Heights  Heights Kleiman bundle Num twist 276a21fa9e53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L169-L186

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53 {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (m : ℕ) :
    bundleNum pp (Function.update L i (twistBundle k x m)) =
      m * bundleNum pp (Function.update L i (twistBundle k x 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bundleNum_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_twist_276a21fa9e53
