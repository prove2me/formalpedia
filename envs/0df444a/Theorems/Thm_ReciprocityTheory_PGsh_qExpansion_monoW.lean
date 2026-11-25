-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_qExpansion_monoW
-- name    : ReciprocityTheory.PGsh.qExpansion_monoW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:22.710607+00:00
-- url     : https://prove2.me/theorems/399b9ede-9382-5d5c-b923-53fba2747968
-- title:
--   PGsh: q Expansion mono W
-- statement:
--   The PGsh construction uses the q Expansion mono W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L29-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

theorem ReciprocityTheory.PGsh.qExpansion_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by sorry
