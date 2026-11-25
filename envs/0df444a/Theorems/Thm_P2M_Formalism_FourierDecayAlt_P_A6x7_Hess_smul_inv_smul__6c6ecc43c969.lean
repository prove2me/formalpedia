-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969
-- name    : P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:48.37219+00:00
-- url     : https://prove2.me/theorems/077276ac-8d5c-405a-a281-e16eb96475dd
-- title:
--   P2 M Formalism Fourier Decay Alt P A6x7 Hess smul inv smul  6c6ecc43c969: P2 M Formalism Fourier Decay Alt P A6x7 Hess smul inv smul  6c6ecc43c969
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A6x7 Hess smul inv smul  6c6ecc43c969 construction uses the P2 M Formalism Fourier Decay Alt P A6x7 Hess smul inv smul  6c6ecc43c969 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L242-L244

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

theorem P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969 (b : Kˣ) {d : ℕ} (x : Fin d → K) :
    (b : K) • (((b⁻¹ : Kˣ) : K) • x) = x := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A6x7».«Hess».«smul_inv_smul'» := P2M_Formalism_FourierDecayAlt_P_A6x7_Hess_smul_inv_smul__6c6ecc43c969
