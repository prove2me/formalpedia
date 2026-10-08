-- Prove2me | Theorems.Thm_QLLL_Valuation_lll_symmetric
-- name    : QLLL.Valuation.lll_symmetric
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:45:43.315883+00:00
-- url     : https://prove2.me/theorems/10648954-846f-4206-bc88-8cdebd055944
-- title:
--   Abstract Lovász Local Lemma for valuations on a bounded lattice (symmetric form)
-- statement:
--   Let $L$ be a bounded lattice and let $R : L \to \mathbb{R}$ be a *valuation*: $R$ is nonnegative, monotone and modular, $R(x) + R(y) = R(x \vee y) + R(x \wedge y)$, with $R(\top) = 1$ and $R(\bot) = 0$ (definition bundle `QLLL_LocalLemma_Basic`). Meets $x \wedge y$ play the role of intersections of events or subspaces.
--
--   Let $X_1, \dots, X_n \in L$ and let $\Gamma(1), \dots, \Gamma(n) \subseteq \{1, \dots, n\}$ form a *dependency graph*: for every $i$ and every set $S$ of indices with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$,
--   $$R\Big(X_i \wedge \bigwedge_{j \in S} X_j\Big) = R(X_i)\, R\Big(\bigwedge_{j \in S} X_j\Big).$$
--
--   Suppose every $\Gamma(i)$ has at most $d$ elements, that $R(X_i) \ge 1 - p$ for every $i$, and that
--   $$p \cdot e \cdot (d + 1) \ \le\ 1.$$
--   Then
--   $$R\Big(\bigwedge_{i=1}^{n} X_i\Big) \ >\ 0.$$
--
--   This is the symmetric local lemma, Theorem 4 of Ambainis, Kempe and Sattath, stated for an arbitrary valuation. It specialises to the symmetric quantum local lemma `QLLL.quantum_lll_symmetric` and to the symmetric classical local lemma `QLLL.SAT.classical_lll_symmetric`, and it is the form used for the $k$-SAT and $k$-QSAT corollaries.
--
--   **Formalization Note** The index set is `Fin n`. The dependency-graph condition excludes $i$ itself from the independent family (the paper's Definition 12 read literally includes $i$ when $(i,i) \notin E$, which would force $R(X_i) \in \{0,1\}$), and mutual independence is stated in product form rather than through conditional values as in Definition 9; the two agree whenever the conditional is defined. Here $d$ is a natural number and $e$ is Euler's number.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Theorem 4 (abstracted to any valuation satisfying Lemma 8 (i), (ii), (iv))

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib

open QLLL
open Finset
open QLLL.Valuation
variable {α : Type*} [Lattice α] [BoundedOrder α]
variable (R : Valuation α)
variable {n : ℕ} {X : Fin n → α} {Γ : Fin n → Finset (Fin n)} {y : Fin n → ℝ}

theorem QLLL.Valuation.lll_symmetric {p : ℝ} {d : ℕ} (hΓ : R.IsDependencyGraph X Γ)
    (hd : ∀ i, (Γ i).card ≤ d) (hX : ∀ i, 1 - p ≤ R (X i))
    (hp : p * Real.exp 1 * (d + 1) ≤ 1) :
    0 < R (univ.inf X) := by sorry
