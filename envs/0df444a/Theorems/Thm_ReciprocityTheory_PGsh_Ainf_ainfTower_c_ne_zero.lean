-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_ainfTower_c_ne_zero
-- name    : ReciprocityTheory.PGsh.Ainf.ainfTower_c_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:58.360926+00:00
-- url     : https://prove2.me/theorems/37acae26-d81c-5827-91bd-107471b16697
-- title:
--   Ainf: ainf Tower c ne zero
-- statement:
--   The Ainf construction uses the ainf Tower c ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfTower.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfTower.lean#L225-L226

import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem ReciprocityTheory.PGsh.Ainf.ainfTower_c_ne_zero : (ainfTower p O hv ε hε).c ≠ 0 := by sorry
