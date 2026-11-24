-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:11.666799+00:00
-- url     : https://prove2.me/theorems/f4306110-d6d2-4749-b36a-e893ead2f4bd
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x5 map  Heis fdf4803780e5: P2 M Formalism Fourier Decay Alt P B2x5 map  Heis fdf4803780e5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x5 map  Heis fdf4803780e5 construction uses the P2 M Formalism Fourier Decay Alt P B2x5 map  Heis fdf4803780e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L610-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L610-L615

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5 (k r' : ℕ) {Φ : Mt k (1 + r') → Mt k (1 + r')} (hΦ : Measurable Φ) {T : HPar k r' → HPar k r'}
    (hT : MeasurePreserving T volume volume) (h : ∀ x, Φ (heisT k r' x) = heisT k r' (T x)) :
    (μHeis k r').map Φ = μHeis k r' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x5».«map_μHeis» := P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
