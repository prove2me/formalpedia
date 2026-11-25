-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_AAvop_congr__add1803a240c
-- name    : P2M_Formalism_FourierDecayAlt_P_PBG_AAvop_congr__add1803a240c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:00:35.155831+00:00
-- url     : https://prove2.me/theorems/ce6e3905-2028-4ca7-bb28-19a59f421d2b
-- title:
--   P2 M Formalism Fourier Decay Alt P PBG AAvop congr  add1803a240c: P2 M Formalism Fourier Decay Alt P PBG AAvop congr  add1803a240c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBG AAvop congr  add1803a240c construction uses the P2 M Formalism Fourier Decay Alt P PBG AAvop congr  add1803a240c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L171-L174

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
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
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem P2M_Formalism_FourierDecayAlt_P_PBG_AAvop_congr__add1803a240c {m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : m₁ ≤ r) (h₂ : m₂ ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    C3.AAvop k r m₁ h₁ u f g = C3.AAvop k r m₂ h₂ u f g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBG».«AAvop_congr'» := P2M_Formalism_FourierDecayAlt_P_PBG_AAvop_congr__add1803a240c
