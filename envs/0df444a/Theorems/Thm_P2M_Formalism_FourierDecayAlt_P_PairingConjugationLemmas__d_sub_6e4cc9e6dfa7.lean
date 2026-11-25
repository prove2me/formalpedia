-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7
-- name    : P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:32.845421+00:00
-- url     : https://prove2.me/theorems/4ce9eddf-3169-445f-bf3a-50688db4dd20
-- title:
--   P2 M Formalism Fourier Decay Alt P Pairing Conjugation Lemmas  d sub 6e4cc9e6dfa7: P2 M Formalism Fourier Decay Alt P Pairing Conjugation Lemmas  d sub 6e4cc9e6dfa7
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Pairing Conjugation Lemmas  d sub 6e4cc9e6dfa7 construction uses the P2 M Formalism Fourier Decay Alt P Pairing Conjugation Lemmas  d sub 6e4cc9e6dfa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean#L144-L149

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]

theorem P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7 (m m' : Fin (finrank ℤ La) → ℤ) : ψd La (m - m') = ψd La m - ψd La m' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PairingConjugationLemmas».«ψd_sub» := P2M_Formalism_FourierDecayAlt_P_PairingConjugationLemmas__d_sub_6e4cc9e6dfa7
