-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8
-- name    : P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:03.91215+00:00
-- url     : https://prove2.me/theorems/ba4194bc-a98a-4af3-9220-f40a3549cb9b
-- title:
--   P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A0 act path Word  f928c95cb9b8: P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A0 act path Word  f928c95cb9b8
-- statement:
--   The P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A0 act path Word  f928c95cb9b8 construction uses the P2 M Formalism Invariant Factor Paths Gelfand Tsetlin Bases A0 act path Word  f928c95cb9b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L274-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L274-L294

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0

theorem P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8 {A : Type} [CommRing A] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → A) (m : (Matrix (Fin n) (Fin n) A)ˣ) (j : ℕ) :
    pathWord isVec μ c (fun i => if isVec i then Matrix.vecMul (Xr i) (↑m : Matrix (Fin n) (Fin n) A)
        else Matrix.vecMul (Xr i) (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) j =
      actF (pathWord isVec μ c Xr j)
        (if 1 ≤ c then (↑m : Matrix (Fin n) (Fin n) A) else (↑m⁻¹ : Matrix (Fin n) (Fin n) A).transpose) := by sorry

alias «Formalism».«InvariantFactorPaths».«GelfandTsetlinBases».«A0».«act_pathWord'» := P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8
