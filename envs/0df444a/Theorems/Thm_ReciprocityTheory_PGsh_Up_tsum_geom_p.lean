-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_tsum_geom_p
-- name    : ReciprocityTheory.PGsh.Up.tsum_geom_p
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:00.228013+00:00
-- url     : https://prove2.me/theorems/aef1bfa1-93af-4487-ade7-e6f7db144622
-- title:
--   Up: tsum geom p
-- statement:
--   The Up construction uses the tsum geom p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L96-L103

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.tsum_geom_p {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) = 1 / ((p : ℝ) - 1) := by sorry
