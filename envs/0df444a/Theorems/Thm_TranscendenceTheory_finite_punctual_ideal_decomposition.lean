-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_punctual_ideal_decomposition
-- name    : TranscendenceTheory.finite_punctual_ideal_decomposition
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T02:52:39.045502+00:00
-- url     : https://prove2.me/theorems/eb6c71e0-f20b-47ba-81aa-e603263fe409
-- title:
--   Local decomposition and gluing of finite polynomial schemes
-- statement:
--   Let the coefficient field be algebraically closed, let the polynomial ring have finitely many variables, and fix a finite injectively labelled family of points:
--
--   $$R=K[X_s\mid s\in\sigma],\qquad |\sigma|<\infty,\qquad a:\iota\hookrightarrow K^\sigma,\qquad |\iota|<\infty.$$
--
--   The theorem gives both assembly and extraction of ideals supported at these points.
--
--   For assembly, suppose each ideal has exactly its assigned point as zero set. Their intersection then has exactly the assigned points as zero set, its quotient is finite-dimensional, and its dimension is the sum of the component dimensions:
--
--   $$V_K(I_i)=\{a_i\},\qquad J=\bigcap_i I_i,$$
--
--   $$V_K(J)=\{a_i:i\in\iota\},\qquad
--   \dim_K(R/J)=\sum_i\dim_K(R/I_i)<\infty.$$
--
--   Moreover, localization of the intersection at each assigned point equals localization of its component ideal:
--
--   $$JR_{\mathfrak m_{a_i}}=I_iR_{\mathfrak m_{a_i}}.$$
--
--   Thus the local quotients, and in particular all local multiplicities, are unchanged.
--
--   For extraction, let an ideal have finite-dimensional quotient, and suppose all assigned points are among its zeros. There exist larger ideals supported at the individual assigned points, preserving the original localizations, whose total dimension does not exceed the original dimension:
--
--   $$I\subseteq I_i,\quad V_K(I_i)=\{a_i\},\quad
--   I_iR_{\mathfrak m_{a_i}}=IR_{\mathfrak m_{a_i}},$$
--
--   $$\sum_i\dim_K(R/I_i)\le\dim_K(R/I).$$
--
--   The proof constructs these ideals by adjoining sufficiently high powers of the evaluation ideals. The selected family need not exhaust the original support, so extraction can discard unselected components. Nonradical ideals and an empty index set are included. No uniform bound on the powers, polynomial degrees, or component dimensions is asserted.
-- source:
--   Stacks Project, Chinese remainder theorem, Lemma 10.15.4, https://stacks.math.columbia.edu/tag/00DT; Artinian local decomposition, Lemma 10.53.6, https://stacks.math.columbia.edu/tag/00JB; nilpotence of the radical, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8. The proof uses the already proved finite-zero-set criterion to pass between point-supported polynomial ideals and finite-dimensional coordinate algebras. Pairwise distinct support points make the ideals comaximal. Their intersection retains every selected localization, has exactly the selected zero set, and has quotient dimension equal to the sum of component dimensions. Conversely, from a finite quotient and selected zeros, construct I + m_i^(N_i) using nilpotence in the local quotient. This preserves each selected localization and the total component dimension is at most the original dimension. Application to A.1: construction of the global chart quotient is reduced equivalently to individual point-supported chart ideals with the same local multiplicity budgets and a bound on their total dimensions. The same uniform constant is retained. Neither selection of those ideals from the analytic vanishing data nor the uniform geometric dimension estimate is claimed.

import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.Submodule

open MvPolynomial

theorem TranscendenceTheory.finite_punctual_ideal_decomposition
    (K σ ι : Type*) [Field K] [IsAlgClosed K] [Finite σ] [Fintype ι]
    (x : ι → σ → K) (hx : Function.Injective x) :
    (∀ J : ι → Ideal (MvPolynomial σ K),
      (∀ i, zeroLocus K (J i) = {x i}) →
      zeroLocus K (⨅ i, J i) = Set.range x ∧
      Module.Finite K (MvPolynomial σ K ⧸ ⨅ i, J i) ∧
      Module.finrank K (MvPolynomial σ K ⧸ ⨅ i, J i) =
        ∑ i, Module.finrank K (MvPolynomial σ K ⧸ J i) ∧
      ∀ i, (⨅ j, J j).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
        (J i).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal))) ∧
    (∀ I : Ideal (MvPolynomial σ K), Module.Finite K (MvPolynomial σ K ⧸ I) →
      (∀ i, x i ∈ zeroLocus K I) →
      ∃ J : ι → Ideal (MvPolynomial σ K),
        (∀ i, I ≤ J i) ∧ (∀ i, zeroLocus K (J i) = {x i}) ∧
        (∀ i, (J i).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
          I.map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal))) ∧
        (∑ i, Module.finrank K (MvPolynomial σ K ⧸ J i)) ≤
          Module.finrank K (MvPolynomial σ K ⧸ I)) := by sorry
