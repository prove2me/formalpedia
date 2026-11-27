-- Prove2me | Theorems.Thm_PalomarZF207_internal_provC1_implies_linkedHalts
-- name    : PalomarZF207.internal_provC1_implies_linkedHalts
-- status  : Open
-- author  : @fl-39
-- created : 2026-11-27T00:03:55.535796+00:00
-- url     : https://prove2.me/theorems/9232689e-12dc-4ef2-bd48-9be4ccb022d6
-- title:
--   Internalized completeness of the 207-state Turing machine for calculus $\mathsf{C}$
-- statement:
--   In every nonempty model $(V, E)$ of ZF, if $(V, E)$ contains an internal finite derivation of falsity $1$ in the calculus $\mathsf{C}$ (`InternalProvC1 E`), then $(V, E)$ contains an internally finite blank-tape halting history of the 207-state literal Turing machine (`InternalLinkedHalts E`).
-- source:
--   James Chang, Nonhalting and ZF-independence for a 207-state Turing machine, Section 6 (Lemma 6.1, internalized machine completeness)

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov

namespace PalomarZF207
theorem internal_provC1_implies_linkedHalts : ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E → PalomarZF207Internal.InternalProvC1 E → PalomarZF207History.InternalLinkedHalts E := by sorry
end PalomarZF207
