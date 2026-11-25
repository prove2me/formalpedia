-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LowDeg_h1Equiv_pair
-- name    : ReciprocityTheory.Coh.LowDeg.h1Equiv_pair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:09.473547+00:00
-- url     : https://prove2.me/theorems/2651b836-8b95-4c2b-8565-9e6085ff9d09
-- title:
--   Low Deg: h1 Equiv pair
-- statement:
--   The Low Deg construction uses the h1 Equiv pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ComapZeroCoboundariesEqBot.lean#L247-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ComapZeroCoboundariesEqBot.lean#L247-L257

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
open ReciprocityTheory.Coh.LowDeg
variable (M : TRep R G)
variable {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M' : TRep R G'}

theorem ReciprocityTheory.Coh.LowDeg.h1Equiv_pair (P : Pair M M') (x : M.H 1) :
    h1EquivOfOrderTwo M' (P.hom.H 1 x) =
      pairH1DecompositionMap M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (h1EquivOfOrderTwo M x) := by sorry
