-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c
-- name    : P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:39.89485+00:00
-- url     : https://prove2.me/theorems/81397701-40ee-48a5-a174-d518a3d1c2da
-- title:
--   P2 M Formalism Fourier Decay Alt P A6x7 Hess mem mul Lat  081cc429fc9c: P2 M Formalism Fourier Decay Alt P A6x7 Hess mem mul Lat  081cc429fc9c
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A6x7 Hess mem mul Lat  081cc429fc9c construction uses the P2 M Formalism Fourier Decay Alt P A6x7 Hess mem mul Lat  081cc429fc9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L206-L208

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]

theorem P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c (b : Kˣ) (L : AddSubgroup K) (x : K) :
    x ∈ mulLat (b : K) L ↔ ((b⁻¹ : Kˣ) : K) * x ∈ L := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A6x7».«Hess».«mem_mulLat'» := P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_mem_mulLat__081cc429fc9c
