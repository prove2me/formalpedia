-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_cas_mem
-- name    : PositivityTheory.ThKR.Join.cas_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:04:59.075061+00:00
-- url     : https://prove2.me/theorems/7df4a4d6-2a8b-4a09-b59e-eb285fdefb43
-- title:
--   Join: cas mem
-- statement:
--   The Join construction uses the cas mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L141-L145

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.ThKR.Join.cas_mem (act : Mat r s →ₗ[ℂ] Module.End ℂ M) : casK (units act) ∈ Algebra.adjoin ℂ (Set.range act) := by sorry
