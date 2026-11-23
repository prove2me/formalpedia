-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
-- name    : P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:10.4127+00:00
-- url     : https://prove2.me/theorems/4ff60fa4-eeeb-4139-94a7-ac902abe63e2
-- title:
--   P2 M Formalism Dwork Power Series Weights eval  jet Pair Poly 5113198bcf9c: P2 M Formalism Dwork Power Series Weights eval  jet Pair Poly 5113198bcf9c
-- statement:
--   The P2 M Formalism Dwork Power Series Weights eval  jet Pair Poly 5113198bcf9c construction uses the P2 M Formalism Dwork Power Series Weights eval  jet Pair Poly 5113198bcf9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L13-L26

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c {F K : Type} [Field F] [Field K] {σ ι : Type} (φ : F →+* K) (x : σ → K)
    (P : MvPolynomial ι (MvPolynomial σ F)) (Th : MvPowerSeries ι F) :
    MvPolynomial.eval₂ φ x (jetPairPoly P Th) =
      jetPair (MvPolynomial.map (MvPolynomial.eval₂Hom φ x) P) (MvPowerSeries.map φ Th) := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«eval₂_jetPairPoly» := P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
