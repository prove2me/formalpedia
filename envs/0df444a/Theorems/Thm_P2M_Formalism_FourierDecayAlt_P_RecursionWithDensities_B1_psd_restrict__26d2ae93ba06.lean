-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
-- name    : P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:48.660443+00:00
-- url     : https://prove2.me/theorems/f1101a1c-8e26-4e13-a0ba-947d770f46a0
-- title:
--   P2 M Formalism Fourier Decay Alt P Recursion With Densities B1 psd restrict  26d2ae93ba06: P2 M Formalism Fourier Decay Alt P Recursion With Densities B1 psd restrict  26d2ae93ba06
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Recursion With Densities B1 psd restrict  26d2ae93ba06 construction uses the P2 M Formalism Fourier Decay Alt P Recursion With Densities B1 psd restrict  26d2ae93ba06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L599-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L599-L606

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]

theorem P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06 {α : Type} {X : Finset α} (Y : Finset α) {k k' : α → α → ℂ} (hk : PSDOn X k)
    (h1 : ∀ x y, x ∈ X ∧ y ∈ X → k' x y = k x y) (h0 : ∀ x y, ¬ (x ∈ X ∧ y ∈ X) → k' x y = 0) :
    PSDOn Y k' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RecursionWithDensities».«B1».«psd_restrict'» := P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
