-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_boxvol_sum_pairs_sub
-- name    : PositivityTheory.Rg.Rs.boxvol.sum_pairs_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:34.685988+00:00
-- url     : https://prove2.me/theorems/085a217e-3762-43d9-82e3-2962787dafd4
-- title:
--   boxvol: sum pairs sub
-- statement:
--   The boxvol construction uses the sum pairs sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L34-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L34-L62

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.boxvol

theorem PositivityTheory.Rg.Rs.boxvol.sum_pairs_sub (n : ℕ) (x : Fin n → ℝ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ r ∈ Finset.range n, ((r : ℝ) * ((n : ℝ) - r)) *
          (if h : 0 < r ∧ r < n then x ⟨r - 1, by omega⟩ - x ⟨r, h.2⟩ else 0) := by sorry
