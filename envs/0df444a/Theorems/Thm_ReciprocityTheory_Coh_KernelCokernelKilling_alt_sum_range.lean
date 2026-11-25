-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_alt_sum_range
-- name    : ReciprocityTheory.Coh.KernelCokernelKilling.alt_sum_range
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:35.580076+00:00
-- url     : https://prove2.me/theorems/0fb852dd-fbcc-427f-9d72-d890e0862397
-- title:
--   Kernel Cokernel Killing: alt sum range
-- statement:
--   The Kernel Cokernel Killing construction uses the alt sum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ShiftA.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ShiftA.lean#L84-L108

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]

theorem ReciprocityTheory.Coh.KernelCokernelKilling.alt_sum_range (m : ℕ) :
    (1 + ∑ j ∈ Finset.range (2 * m + 1), (-1 : R) ^ (j + 1)) = 0 ∧
      (1 + ∑ j ∈ Finset.range (2 * m + 2), (-1 : R) ^ (j + 1)) = 1 := by sorry
