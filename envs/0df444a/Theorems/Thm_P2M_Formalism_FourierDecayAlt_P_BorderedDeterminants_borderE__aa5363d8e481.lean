-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderE__aa5363d8e481
-- name    : P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderE__aa5363d8e481
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:18.993841+00:00
-- url     : https://prove2.me/theorems/df320627-f195-4f69-a716-39b3383b397a
-- title:
--   P2 M Formalism Fourier Decay Alt P Bordered Determinants border E  aa5363d8e481: P2 M Formalism Fourier Decay Alt P Bordered Determinants border E  aa5363d8e481
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Bordered Determinants border E  aa5363d8e481 construction uses the P2 M Formalism Fourier Decay Alt P Bordered Determinants border E  aa5363d8e481 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L93-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L93-L108

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderE__aa5363d8e481 {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (v : Fin m → Fin n) (hE : GlRel E)
    (hve : ∀ j, v j ≠ e) (u : ℂ) :
    qminor E (bE e v) (bE e v) u = Tm E u e e * qminor E v v (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x)) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«BorderedDeterminants».«borderE'» := P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderE__aa5363d8e481
