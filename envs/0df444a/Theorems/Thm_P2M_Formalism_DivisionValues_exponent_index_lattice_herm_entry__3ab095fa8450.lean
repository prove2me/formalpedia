-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
-- name    : P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:51.177544+00:00
-- url     : https://prove2.me/theorems/2c6c7f8e-cd4f-4488-a9ac-2bcb3aec4bab
-- title:
--   P2 M Formalism Division Values exponent index lattice herm entry  3ab095fa8450: P2 M Formalism Division Values exponent index lattice herm entry  3ab095fa8450
-- statement:
--   The P2 M Formalism Division Values exponent index lattice herm entry  3ab095fa8450 construction uses the P2 M Formalism Division Values exponent index lattice herm entry  3ab095fa8450 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L76-L80

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
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
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm

theorem P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450 {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H) (i j : Fin n) :
    H j i = star (H i j) := by sorry

alias «Formalism».«DivisionValues».«exponent_index_lattice».«herm_entry'» := P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
