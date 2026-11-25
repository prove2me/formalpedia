-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_pt
-- name    : ReciprocityTheory.ChartRestriction.L1.qm_pt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:14.326419+00:00
-- url     : https://prove2.me/theorems/29b7fd40-c0a6-537c-a0d1-0bc3b18eb8d0
-- title:
--   L1: qm pt
-- statement:
--   The L1 construction uses the qm pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalMF.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalMF.lean#L40-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
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

theorem ReciprocityTheory.ChartRestriction.L1.qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by sorry
