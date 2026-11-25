-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_sum_del
-- name    : PositivityTheory.Rg.Sw.SP.Mi.sum_del
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:35.77446+00:00
-- url     : https://prove2.me/theorems/3ed3a590-b60b-4193-9e7c-915662fa82c5
-- title:
--   Mi: sum del
-- statement:
--   The Mi construction uses the sum del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L37-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L37-L71

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]

theorem PositivityTheory.Rg.Sw.SP.Mi.sum_del (ρ : ℕ) :
    ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det =
      -((ρ : Pm R (ρ + 1)) * (Xm R (ρ + 1)).det) := by sorry
