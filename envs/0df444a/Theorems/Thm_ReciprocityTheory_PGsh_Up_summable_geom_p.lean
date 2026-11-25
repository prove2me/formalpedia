-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_summable_geom_p
-- name    : ReciprocityTheory.PGsh.Up.summable_geom_p
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:40.341708+00:00
-- url     : https://prove2.me/theorems/c19ace30-b890-4b31-8c90-91d766562a43
-- title:
--   Up: summable geom p
-- statement:
--   The Up construction uses the summable geom p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L105-L110

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

theorem ReciprocityTheory.PGsh.Up.summable_geom_p {p : ℕ} [Fact p.Prime] (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ)
    (hfB : ∀ n, f n ≤ B) : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * f n := by sorry
