-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_retr_mul
-- name    : ReciprocityTheory.Coh.CCA.retr_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:42.181815+00:00
-- url     : https://prove2.me/theorems/fd762a76-1b75-4062-927b-1eb1e9f107de
-- title:
--   CCA: retr mul
-- statement:
--   The CCA construction uses the retr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorA.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorA.lean#L36-L38

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem ReciprocityTheory.Coh.CCA.retr_mul (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by sorry
