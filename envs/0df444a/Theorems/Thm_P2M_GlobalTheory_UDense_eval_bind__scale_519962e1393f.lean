-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UDense_eval_bind__scale_519962e1393f
-- name    : P2M_GlobalTheory_UDense_eval_bind__scale_519962e1393f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:48.388618+00:00
-- url     : https://prove2.me/theorems/cd8b97d8-63b1-4b81-9881-1c31dd932362
-- title:
--   P2 M Global Theory UDense eval bind  scale 519962e1393f: P2 M Global Theory UDense eval bind  scale 519962e1393f
-- statement:
--   The P2 M Global Theory UDense eval bind  scale 519962e1393f construction uses the P2 M Global Theory UDense eval bind  scale 519962e1393f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPoints.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPoints.lean#L24-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.UDense

theorem P2M_GlobalTheory_UDense_eval_bind__scale_519962e1393f {ι : Type} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by sorry

alias «GlobalTheory».«UDense».«eval_bind₁_scale» := P2M_GlobalTheory_UDense_eval_bind__scale_519962e1393f
