-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderS__abd50ed5d9f5
-- name    : P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderS__abd50ed5d9f5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:18.291796+00:00
-- url     : https://prove2.me/theorems/fb87abdb-dcf5-4d9e-8aea-477842eeff8f
-- title:
--   P2 M Formalism Fourier Decay Alt P Bordered Determinants border S  abd50ed5d9f5: P2 M Formalism Fourier Decay Alt P Bordered Determinants border S  abd50ed5d9f5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Bordered Determinants border S  abd50ed5d9f5 construction uses the P2 M Formalism Fourier Decay Alt P Bordered Determinants border S  abd50ed5d9f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BorderedDeterminants.lean#L76-L91

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

theorem P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderS__abd50ed5d9f5 {n m : ℕ} (E : Fin n → Fin n → A) (es : Fin n) (v : Fin m → Fin n) (hE : GlRel E)
    (hvs : ∀ j, v j ≠ es) (u : ℂ) :
    qminor E (bS v es) (bS v es) u = qminor E v v u * Tm E (u - (m : ℂ)) es es -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«BorderedDeterminants».«borderS'» := P2M_Formalism_FourierDecayAlt_P_BorderedDeterminants_borderS__abd50ed5d9f5
