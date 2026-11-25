-- Prove2me | Theorems.Thm_PositivityTheory_Sph_sb_bound
-- name    : PositivityTheory.Sph.sb_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:26.360279+00:00
-- url     : https://prove2.me/theorems/e7cac9d9-ec9a-4357-9a3b-b65a6022972e
-- title:
--   Sph: sb bound
-- statement:
--   The Sph construction uses the sb bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsVBallSubset.lean#L137-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsVBallSubset.lean#L137-L196

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

theorem PositivityTheory.Sph.sb_bound {m p : Type} [Fintype m] [Fintype p] {Φ : Matrix m p k → ℂ} (h1 : IsLocallyConstant Φ)
    (h2 : HasCompactSupport Φ) :
    ∃ t : k, t ≠ 0 ∧ t ∈ 𝒪[k] ∧ (∀ Y, Φ Y ≠ 0 → IntM (t • Y)) ∧ ∀ Y Z, IntM Z → Φ (Y + t • Z) = Φ Y := by sorry
