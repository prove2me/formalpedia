-- Prove2me | Theorems.Thm_PositivityTheory_KReal_CasGl_casK_eq_sum
-- name    : PositivityTheory.KReal.CasGl.casK_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:13.095344+00:00
-- url     : https://prove2.me/theorems/8abc708a-3949-5f95-828c-6ca3e0e7c575
-- title:
--   Cas Gl: cas K eq sum
-- statement:
--   The Cas Gl construction uses the cas K eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean#L31-L33

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

theorem PositivityTheory.KReal.CasGl.casK_eq_sum {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) :
    casK ρ = ∑ k : KI r s, ρ k.1.1 k.1.2 * ρ (swK k).1.1 (swK k).1.2 := by sorry
