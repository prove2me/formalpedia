-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_key
-- name    : PositivityTheory.Rg.Sw.WR.G.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:20.4618+00:00
-- url     : https://prove2.me/theorems/12876ed0-9ae2-49ed-8ea5-953757d462c5
-- title:
--   G: key
-- statement:
--   The G construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L158-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L158-L241

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open GM

theorem PositivityTheory.Rg.Sw.WR.G.key (hI : IntegP) (hW : Wick) (hR : Rot) (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ P : PX m n, ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y := by sorry
