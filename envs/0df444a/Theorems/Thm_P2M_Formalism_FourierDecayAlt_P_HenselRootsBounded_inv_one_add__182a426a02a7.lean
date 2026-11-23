-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7
-- name    : P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:56.717519+00:00
-- url     : https://prove2.me/theorems/f2a075e0-9642-4d30-9139-446236253b8a
-- title:
--   P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded inv one add  182a426a02a7: P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded inv one add  182a426a02a7
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded inv one add  182a426a02a7 construction uses the P2 M Formalism Fourier Decay Alt P Hensel Roots Bounded inv one add  182a426a02a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L234-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L234-L241

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7 (h : Ctx K R ϖ) {k : ℤ} (hk : 1 ≤ k) {u : K} (hu : u ∈ Pk R ϖ k) :
    ∃ u' ∈ Pk R ϖ k, (1 + u) * (1 + u') = 1 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HenselRootsBounded».«inv_one_add'» := P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7
