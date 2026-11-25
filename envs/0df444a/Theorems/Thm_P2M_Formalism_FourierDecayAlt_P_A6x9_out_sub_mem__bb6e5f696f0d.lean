-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d
-- name    : P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:51.164372+00:00
-- url     : https://prove2.me/theorems/d8eac5f2-be84-4060-8ae6-8fa9dc4b6a62
-- title:
--   P2 M Formalism Fourier Decay Alt P A6x9 out sub mem  bb6e5f696f0d: P2 M Formalism Fourier Decay Alt P A6x9 out sub mem  bb6e5f696f0d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A6x9 out sub mem  bb6e5f696f0d construction uses the P2 M Formalism Fourier Decay Alt P A6x9 out sub mem  bb6e5f696f0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L507-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L507-L512

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)

theorem P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d {B : AddSubgroup K} (z : K) :
    (Quotient.out ((z : K) : K ⧸ B) : K) - z ∈ B := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A6x9».«out_sub_mem'» := P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d
