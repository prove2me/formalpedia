-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_zeta_val
-- name    : ReciprocityTheory.PGsh.Ainf.zeta_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:47.916728+00:00
-- url     : https://prove2.me/theorems/cb2953ca-c186-5eb8-84d2-772c6224e84a
-- title:
--   Ainf: zeta val
-- statement:
--   The Ainf construction uses the zeta val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L115-L117

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

theorem ReciprocityTheory.PGsh.Ainf.zeta_val (n : ℕ) :
    (((ainfTower p O hv ε hε).ζ n : ((ainfTower p O hv ε hε).O : Type)ˣ) :
      ((ainfTower p O hv ε hε).O : Type)) = zetaV p O ε n := by sorry
