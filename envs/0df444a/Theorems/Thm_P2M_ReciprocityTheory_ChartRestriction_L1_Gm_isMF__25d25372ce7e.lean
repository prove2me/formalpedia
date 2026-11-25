-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_Gm_isMF__25d25372ce7e
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_Gm_isMF__25d25372ce7e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:32.279347+00:00
-- url     : https://prove2.me/theorems/3c4ce660-d91a-4f9a-9d08-7e69da1c26fd
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 Gm is MF  25d25372ce7e: P2 M Reciprocity Theory Chart Restriction L1 Gm is MF  25d25372ce7e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 Gm is MF  25d25372ce7e construction uses the P2 M Reciprocity Theory Chart Restriction L1 Gm is MF  25d25372ce7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronPt.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModKronPt.lean#L33-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQExpEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronPt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem P2M_ReciprocityTheory_ChartRestriction_L1_Gm_isMF__25d25372ce7e {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«Gm_isMF'» := P2M_ReciprocityTheory_ChartRestriction_L1_Gm_isMF__25d25372ce7e
