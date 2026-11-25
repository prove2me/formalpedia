-- Prove2me | Theorems.Thm_PositivityTheory_KReal_pair_of
-- name    : PositivityTheory.KReal.pair_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:00.689381+00:00
-- url     : https://prove2.me/theorems/9f6d5360-2c2b-5528-965c-5167ab4ad97b
-- title:
--   KReal: pair of
-- statement:
--   The KReal construction uses the pair of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L69-L83

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CorePair
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

theorem PositivityTheory.KReal.pair_of {p q r s : ℕ} (c0 u v u' v' : ℚ) (h1 : u' + cPair 0 s = c0 - (u + cPair r 0))
    (h2 : v' - cPair 0 s = c0 - (v - cPair r 0))
    (hx : ∃ (x : Pol p q r 0) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix r 0) dx ∧ x ∈ Jset p q r 0 ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q r 0 (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u + cPair r 0) (fun _ => v - cPair r 0) a' : ℚ)) : ℂ) else 0) • x)
    (hy : ∃ (x : Pol p q 0 s) (dx : ℕ), x ≠ 0 ∧ x ∈ homog (Ix p q × Ix 0 s) dx ∧ x ∈ Jset p q 0 s ∧
      ∀ a' b', sameBlock a' b' → fockAct1 p q 0 s (Eab a' b') x =
        (if a' = b' then (((Sum.elim (fun _ => u' + cPair 0 s) (fun _ => v' - cPair 0 s) a' : ℚ)) : ℂ) else 0) • x) :
    PairData p q r s (c0 : ℂ) := by sorry
