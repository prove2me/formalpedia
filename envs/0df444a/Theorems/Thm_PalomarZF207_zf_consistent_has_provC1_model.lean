-- Prove2me | Theorems.Thm_PalomarZF207_zf_consistent_has_provC1_model
-- name    : PalomarZF207.zf_consistent_has_provC1_model
-- status  : Open
-- author  : @fl-39
-- created : 2026-11-27T00:03:58.185799+00:00
-- url     : https://prove2.me/theorems/269d3faa-bde5-4103-b507-364d8b118dcb
-- title:
--   Consistent ZF has a model with an internal $\mathsf{C}$-refutation
-- statement:
--   If `PalomarZF207` is consistent, then there exists a nonempty model $(V, E)$ of ZF containing an internal finite refutation in the calculus $\mathsf{C}$ (`InternalProvC1 E`).
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Lemma 1.3 (Calibration) and Section 8

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov

namespace PalomarZF207
theorem zf_consistent_has_provC1_model : Consistent → ∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E ∧ PalomarZF207Internal.InternalProvC1 E := by sorry
end PalomarZF207
