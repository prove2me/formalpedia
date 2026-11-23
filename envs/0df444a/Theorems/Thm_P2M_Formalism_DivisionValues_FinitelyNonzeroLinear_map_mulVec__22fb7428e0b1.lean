-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
-- name    : P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:33.654587+00:00
-- url     : https://prove2.me/theorems/d6034d79-ca38-4681-bc5c-011112bce505
-- title:
--   P2 M Formalism Division Values Finitely Nonzero Linear map mul Vec  22fb7428e0b1: P2 M Formalism Division Values Finitely Nonzero Linear map mul Vec  22fb7428e0b1
-- statement:
--   The P2 M Formalism Division Values Finitely Nonzero Linear map mul Vec  22fb7428e0b1 construction uses the P2 M Formalism Division Values Finitely Nonzero Linear map mul Vec  22fb7428e0b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L156-L159

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}

theorem P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (A.map j) *ᵥ (fun i => j (x i)) = fun i => j ((A *ᵥ x) i) := by sorry

alias «Formalism».«DivisionValues».«FinitelyNonzeroLinear».«map_mulVec'» := P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
