-- Prove2me | Theorems.Thm_TypeDensity_recip_main
-- name    : TypeDensity.recip_main
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:01:13.479356+00:00
-- url     : https://prove2.me/theorems/a36522de-2174-4eb5-9c17-bce7ca34781a
-- title:
--   **Theorem R (reciprocity).** For `n > 0` and every factorization type `σ`: the universal monic density is the root-law coefficient with `q ↦ 1/q` substituted, `A_{n,σ}(q) = B_{n,σ}(1/q)` (where `B_{n,
-- statement:
--   **Theorem R (reciprocity).** For `n > 0` and every factorization type `σ`: the universal monic density is the root-law coefficient with `q ↦ 1/q` substituted, `A_{n,σ}(q) = B_{n,σ}(1/q)` (where `B_{n,σ}` is the coefficient of `σ` in the root law `rootLaw n`), and the universal projective density is self-reciprocal, `R_{n,σ}(1/q) = R_{n,σ}(q)`; both as identities of rational functions in `q`.
--
--   The certified form also assumed `ValidType σ` and `typeDegree σ = n`, which the proof does not use. The hypothesis `0 < n` is used (`rootLaw 0` is defined separately).
-- source:
--   TypeDensity/Reciprocity/Main.lean#L278-L299

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawCoef_globalLaw_false_eq_recipCoef
import Theorems.Thm_TypeDensity_recipCoef_lawCoef_globalLaw_true
import Theorems.Thm_TypeDensity_lawWf_stateLaw
import Theorems.Thm_TypeDensity_lawWf_globalLaw
import Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_false
import Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_true
import Theorems.Thm_TypeDensity_coeff_recipCoef_lawCoef
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.recip_main (n : ℕ) (hn : 0 < n) (σ : FactorType) :
    (monicExpr n σ).rational =
      ((lawCoeff (rootLaw n) σ).subst (.inv .var)).rational ∧
    (projectiveExpr n σ).rational =
      ((projectiveExpr n σ).subst (.inv .var)).rational := by sorry
