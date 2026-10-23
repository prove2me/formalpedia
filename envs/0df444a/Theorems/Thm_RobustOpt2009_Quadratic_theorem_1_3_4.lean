-- Prove2me | Theorems.Thm_RobustOpt2009_Quadratic_theorem_1_3_4
-- name    : RobustOpt2009.Quadratic.theorem_1_3_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:10.836502+00:00
-- url     : https://prove2.me/theorems/ba7257c9-7d38-4e76-88c7-07ff649e2786
-- title:
--   Theorem 1.3.4 — conic representation of a robust linear constraint
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a closed convex pointed cone with nonempty interior, and let $Z=\{\zeta:\exists u,\ P\zeta+Qu+c\in K\}$. Assume either that $K$ has a finite homogeneous inequality representation or that the lifted conic representation is strictly feasible. For arbitrary affine uncertain coefficients $a(\zeta)=a^0+\sum_\ell\zeta_\ell a^\ell$ and $b(\zeta)=b^0+\sum_\ell\zeta_\ell b^\ell$, and every $x$, the assertion is
--   $$[\forall\zeta\in Z,\ a(\zeta)^Tx\le b(\zeta)]\iff\exists v\in K^*: c^Tv+(a^0)^Tx\le b^0,\ Q^Tv=0,\ (P^Tv)_\ell+(a^\ell)^Tx=b^\ell\ \forall\ell.$$
--   This is the lifted conic representation used to dualize the right side of the robust CQI.
--
--   **Formalization Note** The faithful item preserves the literal hypotheses on printed p. 20, without adding nonemptiness of $Z$ in the polyhedral case. Finding F4 gives an empty-set counterexample to that literal reading. The corrected item makes the missing nonemptiness condition explicit. No full-column-rank assumption is imposed; $c$ denotes the source's vector $p$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 1.3.4, printed p. 20 (PDF p. 46).

import Mathlib

open Matrix
open scoped BigOperators

namespace RobustOpt2009.Quadratic

/-- Theorem 1.3.4, printed p. 20, including the polyhedral exception.
Literal statement: the page does not explicitly require nonempty Z.
Finding F4 records the empty-polyhedral-set counterexample; the faithful statement is retained. -/
theorem theorem_1_3_4 {n m r s : ℕ} (K : Set (Fin m → ℝ))
    (hK : (K.Nonempty ∧ (∀ z ∈ K, ∀ w ∈ K, z + w ∈ K) ∧
      (∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t • z ∈ K)) ∧
      (∀ z ∈ K, -z ∈ K → z = 0) ∧ IsClosed K ∧ (interior K).Nonempty)
    (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin m) (Fin s) ℝ)
    (c : Fin m → ℝ)
    (hreg : (∃ (h : ℕ) (H : Matrix (Fin h) (Fin m) ℝ),
      K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}) ∨
      ∃ ζ u, P *ᵥ ζ + Q *ᵥ u + c ∈ interior K)
    (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin r → Fin n → ℝ) (b : Fin r → ℝ)
    (x : Fin n → ℝ) :
    (∀ ζ : Fin r → ℝ, (∃ u, P *ᵥ ζ + Q *ᵥ u + c ∈ K) →
      (a0 + ∑ l, ζ l • a l) ⬝ᵥ x ≤ b0 + ζ ⬝ᵥ b) ↔
    ∃ v : Fin m → ℝ,
      c ⬝ᵥ v + a0 ⬝ᵥ x ≤ b0 ∧ Qᵀ *ᵥ v = 0 ∧
      (∀ l, (Pᵀ *ᵥ v) l + a l ⬝ᵥ x = b l) ∧
      (∀ z ∈ K, 0 ≤ v ⬝ᵥ z) := by sorry

end RobustOpt2009.Quadratic
