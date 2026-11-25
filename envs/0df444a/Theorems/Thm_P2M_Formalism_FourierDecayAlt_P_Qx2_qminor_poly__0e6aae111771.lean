-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_qminor_poly__0e6aae111771
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx2_qminor_poly__0e6aae111771
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:06.519484+00:00
-- url     : https://prove2.me/theorems/c96fd237-ce56-4ab3-b923-7cc6ffb96a1f
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx2 qminor poly  0e6aae111771: P2 M Formalism Fourier Decay Alt P Qx2 qminor poly  0e6aae111771
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx2 qminor poly  0e6aae111771 construction uses the P2 M Formalism Fourier Decay Alt P Qx2 qminor poly  0e6aae111771 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L705-L708
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L705-L708

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem P2M_Formalism_FourierDecayAlt_P_Qx2_qminor_poly__0e6aae111771 (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) {x : Mx k r}
    (hx : x ∈ Glev k r i ∩ D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (s : ℂ) :
    PolyAt (t + 1) (fun Y => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) (Y + s) f x) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx2».«qminor_poly'» := P2M_Formalism_FourierDecayAlt_P_Qx2_qminor_poly__0e6aae111771
