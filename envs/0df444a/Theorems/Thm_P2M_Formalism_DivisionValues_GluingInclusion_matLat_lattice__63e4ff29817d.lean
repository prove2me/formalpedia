-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d
-- name    : P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:33.626292+00:00
-- url     : https://prove2.me/theorems/48b6cfd7-cb08-434c-b589-ae719486cdf3
-- title:
--   P2 M Formalism Division Values Gluing Inclusion mat Lat lattice  63e4ff29817d: P2 M Formalism Division Values Gluing Inclusion mat Lat lattice  63e4ff29817d
-- statement:
--   The P2 M Formalism Division Values Gluing Inclusion mat Lat lattice  63e4ff29817d construction uses the P2 M Formalism Division Values Gluing Inclusion mat Lat lattice  63e4ff29817d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L231-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L231-L241

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d {n D : ℕ} (P : Matrix (Fin D) (Fin n) K)
    (hP : Function.Surjective P.mulVec) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K (matLat P M) := by sorry

alias «Formalism».«DivisionValues».«GluingInclusion».«matLat_lattice'» := P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d
