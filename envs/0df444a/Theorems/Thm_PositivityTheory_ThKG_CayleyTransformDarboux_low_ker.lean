-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_low_ker
-- name    : PositivityTheory.ThKG.CayleyTransformDarboux.low_ker
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:13.698812+00:00
-- url     : https://prove2.me/theorems/90daecd5-2c88-5e89-9a66-e9bd65018d30
-- title:
--   Cayley Transform Darboux: low ker
-- statement:
--   The Cayley Transform Darboux construction uses the low ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean#L84-L90

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKG.CayleyTransformDarboux.low_ker {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {lam : ℂ} (D : M →ₗ[ℂ] M')
    (hD : ∀ x, D (T x) = lam • D x) : low T lam ≤ LinearMap.ker D := by sorry
