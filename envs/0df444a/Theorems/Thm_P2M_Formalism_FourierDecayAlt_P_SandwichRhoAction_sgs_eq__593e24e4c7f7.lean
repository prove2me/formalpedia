-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7
-- name    : P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:58.691033+00:00
-- url     : https://prove2.me/theorems/4b9a1db2-9301-4455-abf8-5d077ab2685b
-- title:
--   P2 M Formalism Fourier Decay Alt P Sandwich Rho Action sgs eq  593e24e4c7f7: P2 M Formalism Fourier Decay Alt P Sandwich Rho Action sgs eq  593e24e4c7f7
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Sandwich Rho Action sgs eq  593e24e4c7f7 construction uses the P2 M Formalism Fourier Decay Alt P Sandwich Rho Action sgs eq  593e24e4c7f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SandwichRhoAction.lean#L56-L59

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SandwichRhoAction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7 (p : SS k r) (x : Mat k r) : sgs p x = (sL p)⁻¹ * x * sR p := by sorry

alias «Formalism».«FourierDecayAlt».«P».«SandwichRhoAction».«sgs_eq'» := P2M_Formalism_FourierDecayAlt_P_SandwichRhoAction_sgs_eq__593e24e4c7f7
