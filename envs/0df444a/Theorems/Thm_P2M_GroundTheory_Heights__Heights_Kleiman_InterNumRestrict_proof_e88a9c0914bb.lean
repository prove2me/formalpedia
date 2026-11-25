-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_proof_e88a9c0914bb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_proof_e88a9c0914bb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:29.393076+00:00
-- url     : https://prove2.me/theorems/6ad0967b-0f8e-550d-bb3f-c9e50bc87d43
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict proof e88a9c0914bb: P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict proof e88a9c0914bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict proof e88a9c0914bb construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict proof e88a9c0914bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumRestrict.lean#L34-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumRestrict.lean#L34-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c

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
open GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_proof_e88a9c0914bb (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumRestrict».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_proof_e88a9c0914bb
