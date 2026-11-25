-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Be2_ker_ainfTower_zero
-- name    : ReciprocityTheory.PGsh.Be2.ker_ainfTower_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:43:48.36062+00:00
-- url     : https://prove2.me/theorems/b0842450-b87a-4413-9f2b-a748092fedef
-- title:
--   Be2: ker ainf Tower zero
-- statement:
--   The Be2 construction uses the ker ainf Tower zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SurjectiveAinfTowerZero.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SurjectiveAinfTowerZero.lean#L20-L27

import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem ReciprocityTheory.PGsh.Be2.ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by sorry
