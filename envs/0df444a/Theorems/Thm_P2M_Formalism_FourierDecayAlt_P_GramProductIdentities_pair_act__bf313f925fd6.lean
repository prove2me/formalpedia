-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6
-- name    : P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:37.267796+00:00
-- url     : https://prove2.me/theorems/66cc0023-9fd0-42f5-add7-90129b3ea2f0
-- title:
--   P2 M Formalism Fourier Decay Alt P Gram Product Identities pair act  bf313f925fd6: P2 M Formalism Fourier Decay Alt P Gram Product Identities pair act  bf313f925fd6
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Gram Product Identities pair act  bf313f925fd6 construction uses the P2 M Formalism Fourier Decay Alt P Gram Product Identities pair act  bf313f925fd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean#L38-L40

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6 (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X X' : Ix S → V) :
    pair ρ X (act M X') = pair ρ (act (star M) X) X' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«GramProductIdentities».«pair_act'» := P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6
