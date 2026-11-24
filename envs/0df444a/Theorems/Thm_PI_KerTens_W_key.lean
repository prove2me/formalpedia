-- Prove2me | Theorems.Thm_PI_KerTens_W_key
-- name    : PI.KerTens.W.key
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:16.310323+00:00
-- url     : https://prove2.me/theorems/8ee61718-dbd7-4f06-9c55-1161c3dcb91b
-- title:
--   W: key
-- statement:
--   The W construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/TensSpans.lean#L27-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/TensSpans.lean#L27-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)

theorem PI.KerTens.W.key (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    (θ : (n → ℂ) → ℂ)
    (hyp : ∀ F ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ)
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (t0 : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) :
    F z * θ t0 ^ s.card = (∏ b ∈ s, θ (part z b)) * F (repl t0 s z) := by sorry
