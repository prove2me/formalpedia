-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_exists_eq_const_mul
-- name    : PositivityTheory.RgUd.T2.HaarDistr.exists_eq_const_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:10.718506+00:00
-- url     : https://prove2.me/theorems/fe80d560-32f0-5078-80e2-119ce3026e1e
-- title:
--   Haar Distr: exists eq const mul
-- statement:
--   The Haar Distr construction uses the exists eq const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L85-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/HaarDistr.lean#L85-L118

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem PositivityTheory.RgUd.T2.HaarDistr.exists_eq_const_mul (Φ Ψ : SB G →ₗ[ℂ] ℂ)
    (hΦ : ∀ (g : G) (α : SB G), Φ (transl g α) = Φ α)
    (hΨ : ∀ (g : G) (α : SB G), Ψ (transl g α) = Ψ α)
    (h0 : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), Ψ (ind K hK) ≠ 0) :
    ∃ c : ℂ, ∀ α : SB G, Φ α = c * Ψ α := by sorry
