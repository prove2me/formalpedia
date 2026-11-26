-- Prove2me | Theorems.Thm_PalomarZF207_physicalHalts_implies_inconsistent
-- name    : PalomarZF207.physicalHalts_implies_inconsistent
-- status  : Open
-- author  : @fl-39
-- created : 2026-11-26T18:34:28.691607+00:00
-- url     : https://prove2.me/theorems/31bbcef9-b238-542d-bd9b-3431df7ef280
-- title:
--   ZF207: physical halting of the 207-state machine implies ZF inconsistency
-- statement:
--   If the literal 207-state binary Turing machine defined by `PalomarZF207History.literalRows` halts in finitely many steps from the all-blank tape configuration $(0, 0, 0)$, then $\mathrm{ZF}$ is inconsistent (i.e., $\bot$ is provable from the $\mathrm{ZF}$ axioms):
--
--   $$\mathrm{PhysicalHalts207} \;\longrightarrow\; \neg \mathrm{Consistent}.$$
--
--   This theorem isolates the machine-specific soundness half of Theorem 1.2(2): the 207-state Turing machine halts only if it finds a valid derivation of contradiction in $\mathrm{ZF}$.
-- source:
--   James Chang, 'Nonhalting and ZF-independence for a 207-state Turing machine' (2026), Theorem 1.2(2); https://github.com/jamesyc/BusyBeaver/blob/37861b991bb70dbaee7dbd91120ab533cba658e2/ZF207/ProofSources/Literal207SigmaSoundness.lean#L36-L57

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement
import Definitions.Def_palomar_zf207_physical

namespace PalomarZF207

theorem physicalHalts_implies_inconsistent : PhysicalHalts207 → ¬ Consistent := by sorry

end PalomarZF207
