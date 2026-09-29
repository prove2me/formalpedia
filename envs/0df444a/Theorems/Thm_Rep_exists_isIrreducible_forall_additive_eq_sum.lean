-- Prove2me | Theorems.Thm_Rep_exists_isIrreducible_forall_additive_eq_sum
-- name    : Rep.exists_isIrreducible_forall_additive_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5e73d0e8-0e82-504c-be62-d4a58dcc6b1e
-- title:
--   Additive functions on a pair of representations
-- statement:
--   Let $k$ be a field, $G$ a group, and let $A$ and $B$ be objects of $\mathrm{Rep}_k(G)$ (representations of $G$ on $k$-vector spaces in the lowest universe) that are finite-dimensional over $k$. The assertion is that there exist a natural number $r$, a family $S : \mathrm{Fin}\,r \to \mathrm{Rep}_k(G)$ and two families of natural numbers $a, b : \mathrm{Fin}\,r \to \mathbb{N}$ with the following three properties. First, each $S_i$ is finite-dimensional over $k$ and its underlying representation $(S_i).\rho$ is irreducible. Second, the $S_i$ are pairwise non-isomorphic in the sense that whenever there exists an isomorphism $S_i \cong S_j$ in $\mathrm{Rep}_k(G)$, one has $i = j$. Third, for every function $\varphi$ from $\mathrm{Rep}_k(G)$ to $\mathbb{Z}$ which is additive in the following sense — for every short complex $X$ in $\mathrm{Rep}_k(G)$ that is short exact and whose middle term $X_2$ is finite-dimensional over $k$ one has $\varphi(X_2) = \varphi(X_1) + \varphi(X_3)$ — both equalities $\varphi(A) = \sum_i a_i\,\varphi(S_i)$ and $\varphi(B) = \sum_i b_i\,\varphi(S_i)$ hold in $\mathbb{Z}$. Only the existence of such multiplicities is asserted; they are not identified with Jordan–Hölder multiplicities.
--
--   This is the Jordan–Hölder bookkeeping needed to compare two finite-dimensional representations in the Grothendieck group $R_k(G)$: a single list of pairwise non-isomorphic irreducible constituents serves both $A$ and $B$, with integer multiplicities valid simultaneously for all additive $\mathbb{Z}$-valued invariants. It is used by [`Rep.eq_of_additive_of_forall_nonempty_res_iso`](thm.html#Rep.eq_of_additive_of_forall_nonempty_res_iso), where agreement of such invariants forces the two multiplicity vectors to coincide.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_isIrreducible_forall_additive_eq_sum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_isIrreducible_forall_additive_eq_sum
    {k : Type} [Field k] {G : Type} [Group G]
    (A B : Rep.{0} k G) [FiniteDimensional k A] [FiniteDimensional k B] :
    ∃ (r : ℕ) (S : Fin r → Rep.{0} k G) (a b : Fin r → ℕ),
      (∀ i, FiniteDimensional k (S i) ∧ (S i).ρ.IsIrreducible) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      ∀ φ : Rep.{0} k G → ℤ,
        (∀ X : ShortComplex (Rep.{0} k G), X.ShortExact → FiniteDimensional k X.X₂ →
          φ X.X₂ = φ X.X₁ + φ X.X₃) →
        φ A = ∑ i, (a i : ℤ) * φ (S i) ∧ φ B = ∑ i, (b i : ℤ) * φ (S i) := by sorry
