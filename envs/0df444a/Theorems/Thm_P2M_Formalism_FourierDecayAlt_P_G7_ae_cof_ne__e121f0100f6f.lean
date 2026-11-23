-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f
-- name    : P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:21.870583+00:00
-- url     : https://prove2.me/theorems/3ac1a4ce-2e5b-4e43-baaa-42e48ed9a57e
-- title:
--   P2 M Formalism Fourier Decay Alt P G7 ae cof ne  e121f0100f6f: P2 M Formalism Fourier Decay Alt P G7 ae cof ne  e121f0100f6f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P G7 ae cof ne  e121f0100f6f construction uses the P2 M Formalism Fourier Decay Alt P G7 ae cof ne  e121f0100f6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L316-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L316-L326

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f (β t : ℂ) (ht : t ≠ 0) (m : ℕ) :
    ∀ᵐ y ∂((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))),
      Cof (strictUpper y.2.1) y.2.2 t ≠ 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«G7».«ae_cof_ne'» := P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f
