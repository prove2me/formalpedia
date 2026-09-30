-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_box_coordinate_recurrence_reduction
-- name    : WeierstrassEllipticZeta.box_coordinate_recurrence_reduction
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T20:24:20.308659+00:00
-- url     : https://prove2.me/theorems/e4583fd1-89cb-4d8b-a133-bc2b7370d1cf
-- title:
--   Coordinate recurrences reduce every box boundary monomial
-- statement:
--   Let $K$ be a commutative ring, let $\sigma$ be a finite variable set, and fix coordinate bounds $b\in\mathbb N^\sigma$. For each coordinate $i$, let $r_i\in K[\sigma]$ have support contained in $\{k e_i:0\le k\le b_i\}$. Thus $r_i$ involves only the variable $X_i$ and has degree at most $b_i$.
--
--   Define the box and its coordinate boundary by
--   $$S=\{e\in\mathbb N^\sigma:e_i\le b_i\text{ for all }i\},\qquad
--   B=\left(\bigcup_{i\in\sigma}(S+e_i)\right)\setminus S.$$
--   For every $d\in B$, there exists a polynomial $q_d$ supported in $S$ such that, for every ideal $I\subseteq K[\sigma]$,
--   $$\left(X_i^{b_i+1}-r_i\in I\text{ for all }i\right)
--   \quad\Longrightarrow\quad X^d-q_d\in I.$$
--
--   The reduction $q_d$ can be chosen independently of the ideal. Zero bounds, zero recurrence polynomials, and an empty variable set are allowed. No field, domain, or independence hypothesis is required. The theorem supplies all box-boundary reductions from one coordinate recurrence per variable.
-- source:
--   Derived coordinate-recurrence certificate for the frontier https://prove2.me/theorems/1cce73f4-b850-4bca-a245-16357d88ad77. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The box boundary reduction is derived using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Algebra/MvPolynomial/Basic.lean (monomial_add_single, support_mul), Data/Finsupp/Single.lean (erase_same, erase_ne), and closure of ideals under multiplication. The connecting sketch reuses the proved finite_jet_span_interpolation and finite_span_rank_stability_iff theorems. The existence of suitable coordinate relations and the uniform geometric estimate remain open.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Ideal.Basic

open scoped Classical Pointwise

noncomputable section

theorem WeierstrassEllipticZeta.box_coordinate_recurrence_reduction
    (K σ : Type*) [CommRing K] [Fintype σ] [DecidableEq σ]
    (b : σ →₀ ℕ) (r : σ → MvPolynomial σ K)
    (hsupport : ∀ i : σ, ∀ e ∈ (r i).support, e ≤ Finsupp.single i (b i)) :
    let S := Finset.Iic b
    let B := (Finset.univ.biUnion fun i : σ =>
      S.image (fun d => d + Finsupp.single i 1)) \ S
    ∀ d ∈ B, ∃ q : MvPolynomial σ K, q.support ⊆ S ∧
      ∀ I : Ideal (MvPolynomial σ K),
        (∀ i : σ, MvPolynomial.X i ^ (b i + 1) - r i ∈ I) →
          MvPolynomial.monomial d 1 - q ∈ I := by sorry
