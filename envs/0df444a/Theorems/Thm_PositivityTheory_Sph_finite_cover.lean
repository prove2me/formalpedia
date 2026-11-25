-- Prove2me | Theorems.Thm_PositivityTheory_Sph_finite_cover
-- name    : PositivityTheory.Sph.finite_cover
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:54.213856+00:00
-- url     : https://prove2.me/theorems/d847fe7e-f937-4cc8-88bc-da8600ceaaa2
-- title:
--   Sph: finite cover
-- statement:
--   The Sph construction uses the finite cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsVBallSubset.lean#L198-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsVBallSubset.lean#L198-L220

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_ExistsVBallSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.Sph.finite_cover {m p : Type} [Fintype m] [Fintype p] (t : k) (ht : t ≠ 0) :
    ∃ S : Finset (Matrix m p k), ∀ Y, IntM (t • Y) → ∃ y ∈ S, ∃ Z, IntM Z ∧ Y = y + t • Z := by sorry
