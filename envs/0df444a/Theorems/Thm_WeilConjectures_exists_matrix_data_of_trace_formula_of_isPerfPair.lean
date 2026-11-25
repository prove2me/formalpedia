-- Prove2me | Theorems.Thm_WeilConjectures_exists_matrix_data_of_trace_formula_of_isPerfPair
-- name    : WeilConjectures.exists_matrix_data_of_trace_formula_of_isPerfPair
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-25T12:29:06.834879+00:00
-- url     : https://prove2.me/theorems/8c821793-f218-4af3-96d2-1162709ae750
-- title:
--   Trace formula and perfect Frobenius-compatible pairings in coordinates: matrices $\Phi_i$ and invertible Gram matrices with $\Phi_i^{\mathsf T}G\Phi_{2n-i}=c\,G$
-- statement:
--   Let $K$ be a field, $n\in\mathbb N$, $(V_i)_{i\in\mathbb N}$ finite-dimensional $K$-vector spaces with endomorphisms $F_i$, $N\colon\mathbb N\to K$ and $c\in K$. Assume
--
--   1. $N_m=\sum_{i=0}^{2n}(-1)^i\operatorname{Tr}(F_i^m)$ for every $m\ge1$;
--   2. for $0\le i\le 2n$, a perfect pairing $\langle\cdot,\cdot\rangle_i\colon V_i\times V_{2n-i}\to K$ with $\langle F_ix,F_{2n-i}y\rangle_i=c\,\langle x,y\rangle_i$.
--
--   Then there are $d_i\in\mathbb N$ and $d_i\times d_i$ matrices $\Phi_i$ over $K$ such that $N_m=\sum_{i=0}^{2n}(-1)^i\operatorname{Tr}(\Phi_i^m)$ for $m\ge1$, and for each $i\le 2n$ matrices $G$ ($d_i\times d_{2n-i}$) and $H$ ($d_{2n-i}\times d_i$) with $GH=1$, $HG=1$ and $\Phi_i^{\mathsf T}G\,\Phi_{2n-i}=c\,G$.
--
--   The conclusion is purely existential: it does not state how $\Phi_i$ relates to $F_i$ or $d_i$ to $\dim V_i$, and $GH=1$, $HG=1$ force $d_i=d_{2n-i}$; $c$ is arbitrary. (In the proof, $\Phi_i$ is the matrix of $F_i$ in a basis and $G$ the Gram matrix of the $i$-th pairing.) With $c=q^n$ this turns the cohomological data of `WeilConjectures_Etale_WeilData` into the coordinate form of `WeilConjectures.exists_frobenius_cohomology_poincare_duality`.
-- source:
--   Linear algebra (matrix of a linear map and Gram matrix of a bilinear form in bases); used to translate P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), (1.5) and (2.3)–(2.5), into coordinates.

import Mathlib

theorem WeilConjectures.exists_matrix_data_of_trace_formula_of_isPerfPair {K : Type*} [Field K] (n : ℕ)
    (V : ℕ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, V i →ₗ[K] V i) (N : ℕ → K) (c : K)
    (htr : ∀ m, 1 ≤ m → N m =
      ∑ i ∈ Finset.range (2 * n + 1), (-1) ^ i * LinearMap.trace K (V i) (F i ^ m))
    (pair : ∀ i, V i →ₗ[K] V (2 * n - i) →ₗ[K] K)
    (hperf : ∀ i ≤ 2 * n, (pair i).IsPerfPair)
    (hsim : ∀ i ≤ 2 * n, ∀ x y, pair i (F i x) (F (2 * n - i) y) = c * pair i x y) :
    ∃ (d : ℕ → ℕ) (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K),
      (∀ m : ℕ, 0 < m → N m =
        ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace) ∧
      (∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
          (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
          G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = c • G) := by sorry
