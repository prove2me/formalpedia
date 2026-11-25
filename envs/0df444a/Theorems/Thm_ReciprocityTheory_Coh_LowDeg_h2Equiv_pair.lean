-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_LowDeg_h2Equiv_pair
-- name    : ReciprocityTheory.Coh.LowDeg.h2Equiv_pair
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:02.621308+00:00
-- url     : https://prove2.me/theorems/a4a6cff3-683d-5a69-bdf8-82a0bb4f2302
-- title:
--   Low Deg: h2 Equiv pair
-- statement:
--   The Low Deg construction uses the h2 Equiv pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ComapZeroCoboundariesEqBot.lean#L259-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ComapZeroCoboundariesEqBot.lean#L259-L270

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

theorem ReciprocityTheory.Coh.LowDeg.h2Equiv_pair (P : Pair M M') (x : M.H 2) :
    h2EquivOfOrderTwo M' (P.hom.H 2 x) =
      compatiblePairH2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv (h2EquivOfOrderTwo M x) := by sorry
