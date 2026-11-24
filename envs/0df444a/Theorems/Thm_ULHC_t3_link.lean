-- Prove2me | Theorems.Thm_ULHC_t3_link
-- name    : ULHC.t3_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:29.527151+00:00
-- url     : https://prove2.me/theorems/e07c078a-23f9-4a8d-95bd-4122075a7e74
-- title:
--   ULHC: t3 link
-- statement:
--   The ULHC construction uses the t3 link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L317-L452
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L317-L452

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

theorem ULHC.t3_link (h3 : ¬ NoTypeIII V (flipCol F c s (k + 2))) :
    ∃ τ : StripSpec, τ.n = 1 ∧ CR2 V F ⟨c, s, k + 2⟩ τ ∧ ChainOK ⟨c, s, k + 2⟩ τ := by sorry
