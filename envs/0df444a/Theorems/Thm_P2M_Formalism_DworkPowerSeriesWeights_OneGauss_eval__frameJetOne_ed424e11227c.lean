-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
-- name    : P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:59.198567+00:00
-- url     : https://prove2.me/theorems/210fc8a6-8b4a-45cb-8f81-31772330daae
-- title:
--   P2 M Formalism Dwork Power Series Weights One Gauss eval  frame Jet One ed424e11227c: P2 M Formalism Dwork Power Series Weights One Gauss eval  frame Jet One ed424e11227c
-- statement:
--   The P2 M Formalism Dwork Power Series Weights One Gauss eval  frame Jet One ed424e11227c construction uses the P2 M Formalism Dwork Power Series Weights One Gauss eval  frame Jet One ed424e11227c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L147-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L147-L180

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
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
open Formalism.DworkPowerSeriesWeights.OneGauss

theorem P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K]
    (φ : F →+* K) {N0 N1 C : ℕ} (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
    (Y : Fin N0 × Fin N0 → K) :
    MvPolynomial.eval₂ φ Y (frameJetOne p hp I (thetaOne g U sgn ep be)) =
      jetPair (minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)
        (MvPowerSeries.subst
            (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K))
            (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
          _root_.Formalism.DworkPowerSeriesWeights.mvExp (expo (fun x : Fin N0 × Fin N1 => (∑ i : Fin N0 × Fin N1,
              MvPowerSeries.C (frA Y i x) * MvPowerSeries.X i :
                MvPowerSeries (Fin N0 × Fin N1) K)) (φ sgn) (φ ep) (MvPowerSeries.map φ be))) := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«OneGauss».«eval₂_frameJetOne» := P2M_Formalism_DworkPowerSeriesWeights_OneGauss_eval__frameJetOne_ed424e11227c
