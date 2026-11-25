-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:28.494607+00:00
-- url     : https://prove2.me/theorems/ad4519c8-3910-4517-8ccb-045c534999ea
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law Basic sphere Normalize eq 616676863ebf: P2 M Ground Theory Heights  Heights Sphere Law Basic sphere Normalize eq 616676863ebf
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law Basic sphere Normalize eq 616676863ebf construction uses the P2 M Ground Theory Heights  Heights Sphere Law Basic sphere Normalize eq 616676863ebf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic

theorem P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf (N : ℕ) (u : Fin 1 × Fin N → ℂ) :
    (fun j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)) =
      ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ)⁻¹ • firstRow N u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawBasic».«sphereNormalize_eq» := P2M_GroundTheory_Heights__Heights_SphereLawBasic_sphereNormalize_eq_616676863ebf
