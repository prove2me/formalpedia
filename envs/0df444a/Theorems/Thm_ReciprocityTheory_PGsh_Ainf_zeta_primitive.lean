-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_zeta_primitive
-- name    : ReciprocityTheory.PGsh.Ainf.zeta_primitive
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:55.283886+00:00
-- url     : https://prove2.me/theorems/457c5ac6-52a5-5bc4-b051-a760b0558fde
-- title:
--   Ainf: zeta primitive
-- statement:
--   The Ainf construction uses the zeta primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L121-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L121-L137

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
include hv hε

theorem ReciprocityTheory.PGsh.Ainf.zeta_primitive (n : ℕ) : IsPrimitiveRoot (zetaV p O ε n) (p ^ (n + 1)) := by sorry
