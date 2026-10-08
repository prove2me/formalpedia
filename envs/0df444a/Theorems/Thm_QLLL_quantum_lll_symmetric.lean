-- Prove2me | Theorems.Thm_QLLL_quantum_lll_symmetric
-- name    : QLLL.quantum_lll_symmetric
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:30.322834+00:00
-- url     : https://prove2.me/theorems/0a6923bc-fbf3-4479-988e-5635f6ec705e
-- title:
--   Quantum Lovász Local Lemma (symmetric form): $\mathrm{R}(\bigcap_i X_i) > 0$ when $p\,e\,(d+1) \le 1$
-- statement:
--   Let $V$ be a nonzero finite-dimensional vector space over a field $\mathbb{K}$, and for a subspace $X \subseteq V$ write
--   $$\mathrm{R}(X) = \frac{\dim X}{\dim V}$$
--   for its *relative dimension* (Definition 3 of the paper). Let $X_1, \dots, X_n$ be subspaces of $V$ and let $\Gamma(1), \dots, \Gamma(n) \subseteq \{1, \dots, n\}$ form a dependency graph for relative dimension: for every $i$ and every set $S$ of indices with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$, $\mathrm{R}\big(X_i \cap \bigcap_{j \in S} X_j\big) = \mathrm{R}(X_i)\,\mathrm{R}\big(\bigcap_{j \in S} X_j\big)$.
--
--   Suppose every $\Gamma(i)$ has at most $d$ elements, $\mathrm{R}(X_i) \ge 1 - p$ for every $i$, and $p \cdot e \cdot (d+1) \le 1$. Then
--   $$\mathrm{R}\Big(\bigcap_{i=1}^{n} X_i\Big) \ >\ 0,$$
--   that is, the subspaces have a nonzero common vector.
--
--   This is Theorem 4 of Ambainis, Kempe and Sattath, the symmetric quantum local lemma, and the instance of `QLLL.Valuation.lll_symmetric` at relative dimension. It is the form applied to $k$-QSAT.
--
--   **Formalization Note** The statement holds over any field. "Mutually R-independent of all but $d$ of the others" is expressed through a dependency graph with out-degree at most $d$. The index set is `Fin n`. The dependency-graph condition excludes $i$ itself from the independent family (the paper's Definition 12 read literally includes $i$ when $(i,i) \notin E$, which would force $R(X_i) \in \{0,1\}$), and mutual independence is stated in product form rather than through conditional values as in Definition 9; the two agree whenever the conditional is defined.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Theorem 4 (symmetric Quantum Lovász Local Lemma)

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib

open QLLL
open Finset
open Module
variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 V] [Nontrivial V]

theorem QLLL.quantum_lll_symmetric {m : ℕ} {X : Fin m → Submodule 𝕜 V}
    {Γ : Fin m → Finset (Fin m)} {p : ℝ} {d : ℕ}
    (hΓ : (relDimValuation (𝕜 := 𝕜) (V := V)).IsDependencyGraph X Γ)
    (hd : ∀ i, (Γ i).card ≤ d) (hX : ∀ i, 1 - p ≤ relDim (X i))
    (hp : p * Real.exp 1 * (d + 1) ≤ 1) :
    0 < relDim (Finset.univ.inf X) := by sorry
