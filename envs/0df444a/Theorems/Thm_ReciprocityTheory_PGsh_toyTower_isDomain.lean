-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_toyTower_isDomain
-- name    : ReciprocityTheory.PGsh.toyTower_isDomain
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:08.745433+00:00
-- url     : https://prove2.me/theorems/7a4046f1-1315-4957-ac6b-c68280070efa
-- title:
--   PGsh: toy Tower is Domain
-- statement:
--   The PGsh construction uses the toy Tower is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ATowerInh.lean#L171-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ATowerInh.lean#L171-L171

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open ReciprocityTheory ReciprocityTheory.PGsh

theorem ReciprocityTheory.PGsh.toyTower_isDomain (p : ℕ) [Fact p.Prime] : IsDomain ((toyTower p).O : Type) := by sorry
