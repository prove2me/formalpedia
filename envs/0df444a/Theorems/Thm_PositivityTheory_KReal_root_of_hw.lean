-- Prove2me | Theorems.Thm_PositivityTheory_KReal_root_of_hw
-- name    : PositivityTheory.KReal.root_of_hw
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:50.43864+00:00
-- url     : https://prove2.me/theorems/dd6c6d35-3ee2-4b84-950b-d296b2fe3bc6
-- title:
--   KReal: root of hw
-- statement:
--   The KReal construction uses the root of hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreRoot.lean#L18-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreRoot.lean#L18-L135

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreRoot
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
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.root_of_hw {p q r s : ℕ} (c : ℂ) (c0 : ℚ) (hc : c = c0) (La : Ix r s → ℚ)
    (hU : ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) {ν : Ix r s → ℚ} {g : Pol p q r s}
    (hg : g ∈ harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2))
    (hw : IsHW (fockAct2 p q r s) ν g) :
    (∃ a b, ¬ sameBlock a b ∧ RootTo ν a b La) ∧
      degW (cPair p q) ν = degW (cPair r s) (fun _ : Ix p q => c0) + 2 := by sorry
