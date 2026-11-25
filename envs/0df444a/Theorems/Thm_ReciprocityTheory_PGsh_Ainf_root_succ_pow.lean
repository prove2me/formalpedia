-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_root_succ_pow
-- name    : ReciprocityTheory.PGsh.Ainf.root_succ_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:13.804049+00:00
-- url     : https://prove2.me/theorems/efe47e2c-ccd5-5d09-8014-5cc8d134bd1d
-- title:
--   Ainf: root succ pow
-- statement:
--   The Ainf construction uses the root succ pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L101-L104

import Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
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
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem ReciprocityTheory.PGsh.Ainf.root_succ_pow (k : ℕ) : root p O ε (k + 1) ^ p = root p O ε k := by sorry
