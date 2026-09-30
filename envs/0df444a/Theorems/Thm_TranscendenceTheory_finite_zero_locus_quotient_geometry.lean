-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry
-- name    : TranscendenceTheory.finite_zero_locus_quotient_geometry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T01:49:30.158803+00:00
-- url     : https://prove2.me/theorems/0f511bb5-f5b9-44b7-a6d4-32606189921d
-- title:
--   Finite zero sets, finite coordinate algebras, and their support points
-- statement:
--   Let an algebraically closed field and a finite set of indeterminates be given. For every ideal in the polynomial ring, its full coordinate quotient is finite-dimensional if and only if its geometric zero set is finite:
--
--   $$R=K[X_s\mid s\in\sigma],\quad |\sigma|<\infty,\qquad
--   \dim_K(R/I)<\infty\ \Longleftrightarrow\ |V_K(I)|<\infty.$$
--
--   The point-to-prime map is injective:
--
--   $$a\longmapsto\mathfrak m_a=\ker(\operatorname{ev}_a).$$
--
--   Under the equivalent finiteness conditions, every prime ideal containing the original ideal is the evaluation ideal of a unique zero:
--
--   $$I\subseteq\mathfrak p\quad\Longrightarrow\quad
--   \exists!a\in V_K(I),\ \mathfrak p=\mathfrak m_a.$$
--
--   The Lean statement gives existence together with injectivity of the point-to-prime map, hence uniqueness. The ideal need not be radical; the finite-dimensional quotient retains nilpotent multiplicities. The empty zero set, unit ideal, and an empty variable index set are included. This theorem does not bound the quotient dimension in terms of the number of geometric points or provide a degree-uniform estimate.
-- source:
--   Stacks Project, Theorem 10.34.1 (Hilbert Nullstellensatz), https://stacks.math.columbia.edu/tag/00FV; Lemma 10.36.5 (finite type and integral imply finite), https://stacks.math.columbia.edu/tag/02JJ; section 10.53, https://stacks.math.columbia.edu/tag/00J4 (finite-dimensional algebras are Artinian, with finitely many primes, all maximal). The complete theorem proves, for any ideal in finitely many variables over an algebraically closed field, that its full coordinate quotient is finite-dimensional iff its zero set is finite. It also identifies the support primes with unique evaluation points. The ideal need not be radical. Application to the first Weierstrass chart in Senthil Kumar's A.1 multiplicity frontier: replace finite-dimensional quotient data and support primes by a finite zero set and distinct labelled chart points, preserving the ideal, local lengths, dimension and uniform constant exactly. A checked local converse shows this replacement is equivalent. This does not construct the geometric ideal from the high-order vanishing hypotheses or prove the uniform section-dimension bound.

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

open MvPolynomial

theorem TranscendenceTheory.finite_zero_locus_quotient_geometry
    (K σ : Type*) [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) :
    (Module.Finite K (MvPolynomial σ K ⧸ I) ↔ (zeroLocus K I).Finite) ∧
    Function.Injective (pointToPoint (k := K) (K := K) (σ := σ)) ∧
    (Module.Finite K (MvPolynomial σ K ⧸ I) →
      ∀ p : PrimeSpectrum (MvPolynomial σ K), I ≤ p.asIdeal →
        ∃ x : σ → K, x ∈ zeroLocus K I ∧ pointToPoint (k := K) x = p) := by sorry
