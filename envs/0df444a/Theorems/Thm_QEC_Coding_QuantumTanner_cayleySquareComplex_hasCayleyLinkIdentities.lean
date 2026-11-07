-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities
-- name    : QEC.Coding.QuantumTanner.cayleySquareComplex_hasCayleyLinkIdentities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:22:59.703105+00:00
-- url     : https://prove2.me/theorems/a254e890-99f3-4f18-b44e-ac419334ceb9
-- title:
--   Quantum Tanner: cayley Square Complex has Cayley Link Identities
-- statement:
--   The canonical realization satisfies both link transport identities;
--   they are proved from its four corners rather than added as input laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8159-L8174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Goodness.lean#L8159-L8174

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v

theorem QEC.Coding.QuantumTanner.cayleySquareComplex_hasCayleyLinkIdentities
    {G A B : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).HasCayleyLinkIdentities := by sorry
