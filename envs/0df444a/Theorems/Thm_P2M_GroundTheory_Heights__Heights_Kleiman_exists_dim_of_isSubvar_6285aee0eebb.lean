-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:59:57.547556+00:00
-- url     : https://prove2.me/theorems/33cf00c9-4b6d-4ace-8423-35efde3ec22e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists dim of is Subvar 6285aee0eebb: P2 M Ground Theory Heights  Heights Kleiman exists dim of is Subvar 6285aee0eebb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists dim of is Subvar 6285aee0eebb construction uses the P2 M Ground Theory Heights  Heights Kleiman exists dim of is Subvar 6285aee0eebb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L183-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L183-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb {pp : Ideal (Poly k N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ D : ℕ, IsSubvar x (primeOf (S := k) x) D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_dim_of_isSubvar» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb
