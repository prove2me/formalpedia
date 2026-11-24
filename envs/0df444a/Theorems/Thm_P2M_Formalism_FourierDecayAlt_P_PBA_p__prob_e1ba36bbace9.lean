-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9
-- name    : P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:50.470805+00:00
-- url     : https://prove2.me/theorems/eba481a2-1d86-41ac-bab9-1e3f8cb1c477
-- title:
--   P2 M Formalism Fourier Decay Alt P PBA p  prob e1ba36bbace9: P2 M Formalism Fourier Decay Alt P PBA p  prob e1ba36bbace9
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBA p  prob e1ba36bbace9 construction uses the P2 M Formalism Fourier Decay Alt P PBA p  prob e1ba36bbace9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L223-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleOfPlaces.lean#L223-L244

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}

theorem P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9 (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop) :
    TB.IsProb (S.base.Wb n) (pθ S A w θ) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBA».«pθ_prob» := P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9
