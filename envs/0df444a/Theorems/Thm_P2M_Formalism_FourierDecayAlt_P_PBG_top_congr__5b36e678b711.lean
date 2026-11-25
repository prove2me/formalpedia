-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711
-- name    : P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:57.933725+00:00
-- url     : https://prove2.me/theorems/2f110b4c-4f68-481a-a854-e28192a74b8d
-- title:
--   P2 M Formalism Fourier Decay Alt P PBG top congr  5b36e678b711: P2 M Formalism Fourier Decay Alt P PBG top congr  5b36e678b711
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBG top congr  5b36e678b711 construction uses the P2 M Formalism Fourier Decay Alt P PBG top congr  5b36e678b711 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L183-L187

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
include hU₀

theorem P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711 (u : ℂ) (a b : Fin (2 * r + k + 1)) {h₁ h₂ : Mat k r → E}
    (he : ∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) (g : Mat k r) (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    Top (EabH (Hpk k r)) u a b h₁ g = QuantumDeterminants.Top (EabH (Hpk k r)) u a b h₂ g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBG».«top_congr'» := P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711
