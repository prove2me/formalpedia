-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_sum_sub
-- name    : PositivityTheory.KReal.CasGl.sum_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:27.605661+00:00
-- url     : https://prove2.me/theorems/780c2c49-6021-5299-ae5f-4503c8845631
-- title:
--   Cas Gl: sum sub
-- statement:
--   The Cas Gl construction uses the sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L24-L29

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
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
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}

theorem PositivityTheory.KReal.CasGl.sum_sub {N : Type} [AddCommMonoid N] (P : Ix r s → Ix r s → Prop) [∀ a b, Decidable (P a b)]
    (F : Ix r s → Ix r s → N) :
    ∑ k : {ab : Ix r s × Ix r s // P ab.1 ab.2}, F k.1.1 k.1.2 = ∑ a, ∑ b, if P a b then F a b else 0 := by sorry
