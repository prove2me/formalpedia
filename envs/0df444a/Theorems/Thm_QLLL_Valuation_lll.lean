-- Prove2me | Theorems.Thm_QLLL_Valuation_lll
-- name    : QLLL.Valuation.lll
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:34:57.438693+00:00
-- url     : https://prove2.me/theorems/f902dde9-18e7-4880-8672-ccb1bb47a3e1
-- title:
--   Abstract Lovász Local Lemma for valuations on a bounded lattice (asymmetric form)
-- statement:
--   Let $L$ be a bounded lattice and let $R : L \to \mathbb{R}$ be a *valuation*: $R$ is nonnegative, monotone and modular, $R(x) + R(y) = R(x \vee y) + R(x \wedge y)$, with $R(\top) = 1$ and $R(\bot) = 0$ (definition bundle `QLLL_LocalLemma_Basic`). Meets $x \wedge y$ play the role of intersections of events or subspaces.
--
--   Let $X_1, \dots, X_n \in L$ and let $\Gamma(1), \dots, \Gamma(n) \subseteq \{1, \dots, n\}$ form a *dependency graph*: for every $i$ and every set $S$ of indices with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$,
--   $$R\Big(X_i \wedge \bigwedge_{j \in S} X_j\Big) = R(X_i)\, R\Big(\bigwedge_{j \in S} X_j\Big).$$
--
--   Let $y_1, \dots, y_n$ be real numbers with $0 \le y_i < 1$ such that
--   $$R(X_i) \ \ge\ 1 - y_i \prod_{j \in \Gamma(i)} (1 - y_j) \qquad \text{for every } i.$$
--   Then
--   $$R\Big(\bigwedge_{i=1}^{n} X_i\Big) \ \ge\ \prod_{i=1}^{n} (1 - y_i).$$
--
--   This is Theorem 14 of Ambainis, Kempe and Sattath in the generality the paper points to after its proof: only properties (i), (ii) and (iv) of Lemma 8 of relative dimension are used. Taking $R$ to be relative dimension on subspaces gives the quantum local lemma `QLLL.quantum_lll`; taking $R$ to be uniform probability on events gives the classical asymmetric Lovász Local Lemma `QLLL.SAT.classical_lll`.
--
--   **Formalization Note** The index set is `Fin n`. The dependency-graph condition excludes $i$ itself from the independent family (the paper's Definition 12 read literally includes $i$ when $(i,i) \notin E$, which would force $R(X_i) \in \{0,1\}$), and mutual independence is stated in product form rather than through conditional values as in Definition 9; the two agree whenever the conditional is defined.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Theorem 14 (abstracted to any valuation satisfying Lemma 8 (i), (ii), (iv))

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib

open QLLL
open Finset
open QLLL.Valuation
variable {α : Type*} [Lattice α] [BoundedOrder α]
variable (R : Valuation α)
variable {n : ℕ} {X : Fin n → α} {Γ : Fin n → Finset (Fin n)} {y : Fin n → ℝ}

theorem QLLL.Valuation.lll (hΓ : R.IsDependencyGraph X Γ)
    (hy₀ : ∀ i, 0 ≤ y i) (hy₁ : ∀ i, y i < 1)
    (hX : ∀ i, 1 - y i * ∏ j ∈ Γ i, (1 - y j) ≤ R (X i)) :
    ∏ i, (1 - y i) ≤ R (univ.inf X) := by sorry
