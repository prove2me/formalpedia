-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
-- name    : P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:12:16.289293+00:00
-- url     : https://prove2.me/theorems/1e0b5502-e66d-4ab7-af0f-2e38f077ffd2
-- title:
--   P2 M Formalism Fourier Decay Alt P A5x9 Lam mul  36cdfb417c73: P2 M Formalism Fourier Decay Alt P A5x9 Lam mul  36cdfb417c73
-- statement:
--   The P2 M Formalism Fourier Decay Alt P A5x9 Lam mul  36cdfb417c73 construction uses the P2 M Formalism Fourier Decay Alt P A5x9 Lam mul  36cdfb417c73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L462-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L462-L465

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73 (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R) :
    abelian₂ R k Z₀ x = b22 k p *ᵥ abelian₂ R k (Z₀ * p) x := by sorry

alias «Formalism».«FourierDecayAlt».«P».«A5x9».«Lam_mul'» := P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
