-- Prove2me | Theorems.Thm_P2M_N4Code_min__proof_irrel_1e0402de89ff
-- name    : P2M_N4Code_min__proof_irrel_1e0402de89ff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:42.860471+00:00
-- url     : https://prove2.me/theorems/5525c9a5-78ed-5441-bdfc-61158b5074a0
-- title:
--   P2 M N4 Code min  proof irrel 1e0402de89ff: P2 M N4 Code min  proof irrel 1e0402de89ff
-- statement:
--   `Finset.min'` does not depend on the nonemptiness proof.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L26-L27
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L26-L27

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem P2M_N4Code_min__proof_irrel_1e0402de89ff {s : Finset ℕ} (H1 H2 : s.Nonempty) : s.min' H1 = s.min' H2 := by sorry

alias «N4Code».«min'_proof_irrel» := P2M_N4Code_min__proof_irrel_1e0402de89ff
