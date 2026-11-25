-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_a0
-- name    : ReciprocityTheory.PGsh.a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:52.622797+00:00
-- url     : https://prove2.me/theorems/9580bc08-b250-4289-9a91-63bd594b06cb
-- title:
--   PGsh: a0
-- statement:
--   The PGsh construction uses the a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/Imports.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/Imports.lean#L9-L22

import Definitions.Def_ReciprocityTheory_DualLattices_DvdOfCoeffZero
import Definitions.Def_ReciprocityTheory_DualLattices_ValUntiltESubOne
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_ZmodTrichotomy
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh

theorem ReciprocityTheory.PGsh.a0 (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by sorry
