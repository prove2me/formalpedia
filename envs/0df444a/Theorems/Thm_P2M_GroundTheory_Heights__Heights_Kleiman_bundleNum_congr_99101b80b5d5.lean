-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:15.065595+00:00
-- url     : https://prove2.me/theorems/57da6fbf-f108-5035-b7ce-641dbe42082a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bundle Num congr 99101b80b5d5: P2 M Ground Theory Heights  Heights Kleiman bundle Num congr 99101b80b5d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bundle Num congr 99101b80b5d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman bundle Num congr 99101b80b5d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L121-L124

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5 (pp : Ideal (Poly k N)) {n : ℕ} {L L' : Fin n → LineBundle k x}
    (h : ∀ i, (L i).toSubSystem = (L' i).toSubSystem) : bundleNum pp L = bundleNum pp L' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bundleNum_congr» := P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
