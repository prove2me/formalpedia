-- Prove2me | Theorems.Thm_PI_FoldDCUnfold_W_pointwise_of
-- name    : PI.FoldDCUnfold.W.pointwise_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:35.573596+00:00
-- url     : https://prove2.me/theorems/912cf4ce-6d3c-5c06-98ac-d18a76841b3e
-- title:
--   W: pointwise of
-- statement:
--   The W construction uses the pointwise of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FoldingUnfolding/FoldDCUnfoldOf.lean#L14-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FoldingUnfolding/FoldDCUnfoldOf.lean#L14-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_FoldDCUnfoldOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.FoldDCUnfold PI.FoldDCUnfold.W
universe u

theorem PI.FoldDCUnfold.W.pointwise_of (h1 : TransIndep.{u}) (h3 : DCTrans.{u})
    {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (D D' : Set G) (hD : IsRightTransversal Γ S D) (hD' : IsRightTransversal Γ S' D')
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (g h : G → ℝ≥0∞) (hg : ∀ s ∈ S, ∀ y : G, g (s * y) = g y)
    (hh : ∀ s ∈ S', ∀ y : G, h (s * y) = h y) (x : G) :
    (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' p : (E (r : G) × D),
        g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) := by sorry
