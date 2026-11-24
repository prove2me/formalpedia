-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_apply_zero_of_fst
-- name    : PositivityTheory.ThKF0.Chr.schrodinger_apply_zero_of_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:16.553116+00:00
-- url     : https://prove2.me/theorems/2c9e9488-62c4-4af2-9b91-2a47b005f8e5
-- title:
--   Chr: schrodinger apply zero of fst
-- statement:
--   The Chr construction uses the schrodinger apply zero of fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L15-L16

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem PositivityTheory.ThKF0.Chr.schrodinger_apply_zero_of_fst {w : V R κ} (h : w.1 = 0) (φ : (κ → R) → ℂ) : schr ψ w φ 0 = φ 0 := by sorry
