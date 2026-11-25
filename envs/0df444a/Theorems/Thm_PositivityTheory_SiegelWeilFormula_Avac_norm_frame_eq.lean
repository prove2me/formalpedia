-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Avac_norm_frame_eq
-- name    : PositivityTheory.SiegelWeilFormula.Avac.norm_frame_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:50.58528+00:00
-- url     : https://prove2.me/theorems/a2ab39d4-f24e-46ae-9033-ebd091b3c175
-- title:
--   Avac: norm frame eq
-- statement:
--   The Avac construction uses the norm frame eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/VacuumIwasawa/FrameLin.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/VacuumIwasawa/FrameLin.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSumStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_VacuumIwasawa_FrameLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Avac
variable {m : ℕ}

theorem PositivityTheory.SiegelWeilFormula.Avac.norm_frame_eq (hm : 1 ≤ m) (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ)
    (hζ : ζ = 1 ∨ ζ = Complex.I) (hζ' : ζ' = 1 ∨ ζ' = Complex.I)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (h' : ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1)
    (v : Fin m → ℂ) : ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by sorry
