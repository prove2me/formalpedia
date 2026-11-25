-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5
-- name    : P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:58.333901+00:00
-- url     : https://prove2.me/theorems/12c3c268-8325-40d9-bc4d-334831ca5522
-- title:
--   P2 M Formalism Division Values Semilocal Basis Hermitian Twist Divisors mem loc iff  028e821c1df5: P2 M Formalism Division Values Semilocal Basis Hermitian Twist Divisors mem loc iff  028e821c1df5
-- statement:
--   The P2 M Formalism Division Values Semilocal Basis Hermitian Twist Divisors mem loc iff  028e821c1df5 construction uses the P2 M Formalism Division Values Semilocal Basis Hermitian Twist Divisors mem loc iff  028e821c1df5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LocBasis.lean#L14-L18

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.SemilocalBasisHermitianTwistDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5 (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔
      ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal, s • x ∈ M := by sorry

alias «Formalism».«DivisionValues».«SemilocalBasisHermitianTwistDivisors».«mem_loc_iff'» := P2M_Formalism_DivisionValues_SemilocalBasisHermitianTwistDivisors_mem_loc_iff__028e821c1df5
