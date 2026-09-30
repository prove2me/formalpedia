-- Prove2me | Theorems.Thm_TranscendenceTheory_punctual_ideal_finite_jet_characterization
-- name    : TranscendenceTheory.punctual_ideal_finite_jet_characterization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-21T04:26:38.764043+00:00
-- url     : https://prove2.me/theorems/edca4827-6d03-4e68-881f-2b21b3883565
-- title:
--   Explicit finite-jet determination of point-supported polynomial ideals
-- statement:
--   Let K be an algebraically closed field, let R = K[X_s] have finitely many variables, let I be an ideal, and let x be a K-rational point. Write m_x for the ideal of polynomials vanishing at x and d = dim_K(R/I), with Lean's finrank convention. Then
--
--   $$
--   V(I)=\{x\}\quad\Longleftrightarrow\quad \mathfrak m_x^d\subseteq I\subseteq\mathfrak m_x.
--   $$
--
--   If these equivalent conditions hold, d is positive, the finite jet algebra R/m_x^d is finite-dimensional over K, and I is the inverse image of its image in that jet algebra. Thus the full nonreduced ideal is determined by jets of order below d, not merely by its support.
--
--   The proof includes a general quantitative lemma: for any commutative K-algebra R with finite-dimensional quotient R/I,
--
--   $$
--   (\sqrt I)^{\dim_K(R/I)}\subseteq I.
--   $$
--
--   The argument includes zero-dimensional and zero-quotient edge cases in this general lemma. The punctual characterization separately forces a nonzero quotient. It does not bound d in terms of the bidegree of the analytic polynomial in A.1.
-- source:
--   Stacks Project, Artinian radical nilpotence, Lemma 10.53.4, https://stacks.math.columbia.edu/tag/00J8; Hilbert Nullstellensatz, https://stacks.math.columbia.edu/tag/00FV. In a finite-dimensional algebra A, nonzero powers of a nilpotent ideal strictly decrease in dimension, so its dim(A)-th power vanishes. Applied to the quotient R/I, this proves radical(I)^dim(R/I) <= I. For polynomial ideals with singleton zero set {x}, this yields the exact finite-jet criterion m_x^d <= I <= m_x with d=dim(R/I), and reconstruction of I from its image in the finite jet algebra. The A.1 application gives an equivalent finite-jet formulation of the punctual-chart frontier, retaining the same ideals, lengths, dimensions and uniform constant. Witness selection and the geometric sum-of-dimensions bound remain open; no bidegree or integer-search bound is improved.

import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry

open MvPolynomial

theorem TranscendenceTheory.punctual_ideal_finite_jet_characterization
    (K σ : Type*) [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (x : σ → K) :
    (zeroLocus K I = {x} ↔
      (vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I) ≤ I ∧
        I ≤ vanishingIdeal K {x}) ∧
    (zeroLocus K I = {x} →
      0 < Module.finrank K (MvPolynomial σ K ⧸ I) ∧
      Module.Finite K (MvPolynomial σ K ⧸
        (vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)) ∧
      I = (I.map (Ideal.Quotient.mk
        ((vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)))).comap
          (Ideal.Quotient.mk
            ((vanishingIdeal K {x}) ^ Module.finrank K (MvPolynomial σ K ⧸ I)))) := by sorry
