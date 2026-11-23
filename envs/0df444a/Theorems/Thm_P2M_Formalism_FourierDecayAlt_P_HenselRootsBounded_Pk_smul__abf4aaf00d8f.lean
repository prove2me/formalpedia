-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
-- name    : P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:59.562576+00:00
-- url     : https://prove2.me/theorems/74659ad5-ffc1-4fb0-ace2-782f3143e3cc
-- title:
--   P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded Pk smul  abf4aaf00d8f: P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded Pk smul  abf4aaf00d8f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded Pk smul  abf4aaf00d8f construction uses the P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded Pk smul  abf4aaf00d8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L52-L53

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}

theorem P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f {k : ℤ} {x r : K} (hr : r ∈ R) (hx : x ∈ Pk R ϖ k) : r * x ∈ Pk R ϖ k := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HenselRootsBounded».«Pk_smul'» := P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
