-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:30.684637+00:00
-- url     : https://prove2.me/theorems/6f00e7dd-dba1-4b09-9746-dc62f45b8279
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le map cbf637ec4a9e: P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le map cbf637ec4a9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le map cbf637ec4a9e construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite inc Ideal le map cbf637ec4a9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L171-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L171-L188

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    incIdeal I k ≤ (incIdeal (integralModel I) k).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«incIdeal_le_map» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e
