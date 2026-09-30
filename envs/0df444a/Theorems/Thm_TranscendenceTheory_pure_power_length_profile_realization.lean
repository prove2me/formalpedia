-- Prove2me | Theorems.Thm_TranscendenceTheory_pure_power_length_profile_realization
-- name    : TranscendenceTheory.pure_power_length_profile_realization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T05:57:13.558144+00:00
-- url     : https://prove2.me/theorems/17b89009-e8c3-4997-8f2e-ed72b557d77a
-- title:
--   Explicit four-equation realization of prescribed local lengths
-- statement:
--   Let $I$ be a finite index set, let $a_i\in\mathbb C$ be distinct, and let $e_i$ be positive integers. In $R=\mathbb C[t,x,y,u]$, put
--
--   $$F(t)=\prod_{i\in I}(t-a_i)^{e_i},\qquad
--   J=(F(t),x,y,u).$$
--
--   For every monomial order, the four displayed generators have unit leading coefficients and leading exponent vectors
--
--   $$\left(\sum_i e_i\right)\mathbf e_0,\quad
--   \mathbf e_1,\quad\mathbf e_2,\quad\mathbf e_3.$$
--
--   The quotient $R/J$ is finite-dimensional, with
--
--   $$\dim_{\mathbb C}(R/J)=\sum_i e_i.$$
--
--   There is an injective family of primes $p_i$ in its spectrum whose local lengths are finite and exactly $e_i$. The proof constructs these primes from evaluation at $(a_i,0,0,0)$.
--
--   An empty index set is allowed: $F=1$, the quotient is zero, its dimension is zero, and the prime family is empty. Positivity is required for every label that is present. No radical-ideal assumption is imposed.
-- source:
--   Derived explicit length-profile realization for the A.1 certificate in https://prove2.me/theorems/049daeec-3df5-4ef0-9a62-8ff9030ce7f4. Take F(t)=product_i(t-a_i)^(e_i) and J=(F,x,y,u). The unit pure leading powers and the Proved standard-monomial theorem https://prove2.me/theorems/59cb8f12-d4f7-4f7f-ba02-e645e5402da4 give dimension sum_i e_i. Projections onto C[T]/(T^(e_i)) give the local lower lengths; the finite-algebra length sum forces equality. Background: Stacks Project, Lemma 10.53.6, tag 00JB, https://stacks.math.columbia.edu/tag/00JB, Artinian decomposition into prime localizations. The univariate quotient dimension is pinned Mathlib's finrank_quotient_span_eq_natDegree in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean. This is a supporting algebraic construction, not Philippon's global zero estimate. Both frontier directions preserve C, the locus and chart point. Equations and primes become prescribed by the label count and cost; the global inequality and geometric selection remain Open.

import Definitions.Def_WeierstrassEllipticZeta_CurvilinearChartJets
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic

noncomputable section
open MvPolynomial
open scoped MonomialOrder

theorem TranscendenceTheory.pure_power_length_profile_realization
    (ι : Type) [Fintype ι] (a : ι → ℂ) (ha : Function.Injective a)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (o : MonomialOrder (Fin 4)) :
    let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
      ![∏ i, (X 0 - C (a i)) ^ e i, X 1, X 2, X 3]
    let d : Fin 4 → ℕ := ![∑ i, e i, 1, 1, 1]
    let J : Ideal (MvPolynomial (Fin 4) ℂ) := Ideal.span (Set.range b)
    (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
      (∀ i, o.degree (b i) = Finsupp.single i (d i)) ∧
      Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ i, e i ∧
      ∃ p : ι → PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ J),
        Function.Injective p ∧ ∀ i,
          Module.length (Localization.AtPrime (p i).asIdeal)
            (Localization.AtPrime (p i).asIdeal) ≠ ⊤ ∧
          (Module.length (Localization.AtPrime (p i).asIdeal)
            (Localization.AtPrime (p i).asIdeal)).toNat = e i := by sorry
