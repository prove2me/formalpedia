-- Prove2me | Theorems.Thm_PositivityTheory_KReal_exists_gen
-- name    : PositivityTheory.KReal.exists_gen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:37.308469+00:00
-- url     : https://prove2.me/theorems/edc8cfcb-4a76-538d-b8fd-bf51aee9da6d
-- title:
--   KReal: exists gen
-- statement:
--   The KReal construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L110-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreGen.lean#L110-L165

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSplit
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
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
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.exists_gen (c : ℂ) (c0 : ℚ) (hc : c = c0) (La : Ix r s → ℚ)
    (hJ : JointShape p q r s (fun _ => c0) La) (hU : ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) :
    ∃ (d0 : ℕ) (f : Pol p q r s), (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0) ∧
      f ∈ homog (Ix p q × Ix r s) d0 ∧ HwK (units (fockAct2 p q r s)) La f ∧
      ∀ U : Submodule ℂ (Pol p q r s), f ∈ U → KSt (units (fockAct2 p q r s)) U →
        jHarm p q r s ⊓ polChi p q r s c ≤ U := by sorry
