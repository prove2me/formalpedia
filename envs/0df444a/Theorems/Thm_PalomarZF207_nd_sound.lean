-- Prove2me | Theorems.Thm_PalomarZF207_nd_sound
-- name    : PalomarZF207.nd_sound
-- status  : Proved
-- author  : @fl-39
-- created : 2026-11-27T00:02:37.217087+00:00
-- url     : https://prove2.me/theorems/b84c0b21-4d10-420a-aefb-a25ca5cb180d
-- title:
--   Soundness of natural deduction for ZF
-- statement:
--   Every formula $p$ provable in the natural-deduction proof system of `PalomarZF207` holds under every valuation $s : \mathbb{N} \to V$ in every nonempty model $(V, E)$ of ZF.
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Section 1 (standard soundness of first-order natural deduction for ZF)

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

namespace PalomarZF207
theorem nd_sound (p : Formula) : Provable p → ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E → ∀ s : Nat → V, eval E p s := by sorry
end PalomarZF207
