-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_nonempty
-- name    : ReciprocityTheory.PGsh.monoIdx_nonempty
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:16.636493+00:00
-- url     : https://prove2.me/theorems/2778d2cf-7053-5821-bdef-b9e631260807
-- title:
--   PGsh: mono Idx nonempty
-- statement:
--   The PGsh construction uses the mono Idx nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L46-L51

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

theorem ReciprocityTheory.PGsh.monoIdx_nonempty {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by sorry
