-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_icompL
-- name    : PositivityTheory.Rg.Sw.LVs.CK.icompL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:05.835823+00:00
-- url     : https://prove2.me/theorems/6ec3faf4-e22f-41ef-b575-6429b2b65ec0
-- title:
--   CK: icomp L
-- statement:
--   The CK construction uses the icomp L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L41-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L41-L64

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.CK.icompL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (G : F → ℂ) (φ : E → F) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (x : E) (y : F) (hxy : φ x = y) (hG : AnalyticAt ℂ G y) (n : ℕ) (u : Fin n → E)
    (v : Fin n → F) (huv : ∀ i, φ (u i) = v i) :
    iteratedFDeriv ℂ n (G ∘ φ) x u = iteratedFDeriv ℂ n G y v := by sorry
