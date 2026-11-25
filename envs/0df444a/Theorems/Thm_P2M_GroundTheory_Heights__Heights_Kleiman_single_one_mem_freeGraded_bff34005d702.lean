-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:48.669344+00:00
-- url     : https://prove2.me/theorems/a39fdc7f-7874-455e-b955-a2bfadad8fa9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman single one mem free Graded bff34005d702: P2 M Ground Theory Heights  Heights Kleiman single one mem free Graded bff34005d702
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman single one mem free Graded bff34005d702 construction uses the P2 M Ground Theory Heights  Heights Kleiman single one mem free Graded bff34005d702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L145-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L145-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702 {r : ℕ} (deg : Fin r → ℤ) (j : Fin r) :
    (Pi.single j 1 : Fin r → Poly S N) ∈ (freeGraded S N deg).piece (deg j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«single_one_mem_freeGraded» := P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702
