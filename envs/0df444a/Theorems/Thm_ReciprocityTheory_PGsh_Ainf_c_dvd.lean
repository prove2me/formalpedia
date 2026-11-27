-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Ainf_c_dvd
-- name    : ReciprocityTheory.PGsh.Ainf.c_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:08.80736+00:00
-- url     : https://prove2.me/theorems/ffbdc332-df14-4a20-8b69-a37cdc49ef2d
-- title:
--   Ainf: c dvd
-- statement:
--   The Ainf construction uses the c dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemOfCompat.lean#L147-L152

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

theorem ReciprocityTheory.PGsh.Ainf.c_dvd (c' : O) (h : v (algebraMap O C c') ^ (p - 1) ≤ v (p : C)) :
    fontaineTheta O p (nu p O ε) ∣ c' := by sorry
