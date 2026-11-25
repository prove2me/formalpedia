-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_AAop_congr__23af70070c46
-- name    : P2M_Formalism_FourierDecayAlt_P_PBG_AAop_congr__23af70070c46
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:08:36.779854+00:00
-- url     : https://prove2.me/theorems/b0ea8cb1-3517-5d97-b744-d1043db5390b
-- title:
--   P2 M Formalism Fourier Decay Alt P PBG AAop congr  23af70070c46: P2 M Formalism Fourier Decay Alt P PBG AAop congr  23af70070c46
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBG AAop congr  23af70070c46 construction uses the P2 M Formalism Fourier Decay Alt P PBG AAop congr  23af70070c46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L166-L169

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

theorem P2M_Formalism_FourierDecayAlt_P_PBG_AAop_congr__23af70070c46 {m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : m₁ ≤ r) (h₂ : m₂ ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    C3.AAop k r m₁ h₁ u f g = C3.AAop k r m₂ h₂ u f g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBG».«AAop_congr'» := P2M_Formalism_FourierDecayAlt_P_PBG_AAop_congr__23af70070c46
