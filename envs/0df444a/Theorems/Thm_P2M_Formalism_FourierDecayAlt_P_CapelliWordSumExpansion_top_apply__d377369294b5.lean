-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5
-- name    : P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:23.973711+00:00
-- url     : https://prove2.me/theorems/0442aa76-efac-4bb1-bf22-f5fd52cc048b
-- title:
--   P2 M Formalism Fourier Decay Alt P Capelli Word Sum Expansion top apply  d377369294b5: P2 M Formalism Fourier Decay Alt P Capelli Word Sum Expansion top apply  d377369294b5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Capelli Word Sum Expansion top apply  d377369294b5 construction uses the P2 M Formalism Fourier Decay Alt P Capelli Word Sum Expansion top apply  d377369294b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L139-L141

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5 (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (g : Mat k r) :
    Top Eop u c d f g = (if c = d then u • f g else 0) + Eop c d f g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«CapelliWordSumExpansion».«top_apply'» := P2M_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_top_apply__d377369294b5
