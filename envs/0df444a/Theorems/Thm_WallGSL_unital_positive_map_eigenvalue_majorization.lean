-- Prove2me | Theorems.Thm_WallGSL_unital_positive_map_eigenvalue_majorization
-- name    : WallGSL.unital_positive_map_eigenvalue_majorization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:36:27.641726+00:00
-- url     : https://prove2.me/theorems/1dbff5b2-2399-4c34-abd0-65babe8f1b39
-- title:
--   Theorem 5 (Wall 2013): eigenvalue majorization under positive unital trace-preserving maps
-- statement:
--   **Theorem 5 (appendix).** Let $\rho$ be an $n\times n$ density matrix (positive semidefinite, trace $1$) and let $T$ be a linear map on $n\times n$ complex matrices that is **positive** (maps positive semidefinite matrices to positive semidefinite matrices), **trace preserving** and **identity preserving** ($T(I)=I$). Then for every $i$, the sum of the $i$ largest eigenvalues of $T(\rho)$ is at most the sum of the $i$ largest eigenvalues of $\rho$:
--   $$\sum_{j=1}^{i}\lambda^{\downarrow}_j\big(T(\rho)\big)\ \le\ \sum_{j=1}^{i}\lambda^{\downarrow}_j(\rho).$$
--   In the paper's notation, $\operatorname{tr}(Q\,T(\rho)\,Q)\le\operatorname{tr}(P\rho P)$, where $P$ and $Q$ project onto the eigenspaces of the $i$ largest eigenvalues of $\rho$ and of $T(\rho)$.
--
--   This is the statement that probability eigenvalues can only evolve towards equalization, which underlies the coarse-grained second law discussed in §2.1.
--
--   **Formalization Note** "The sum of the $i$ largest eigenvalues" is expressed without sorting: every sum of $i$ eigenvalues of $T(\rho)$ (indexed by a set $s$ of size $i$) is bounded by some sum of $i$ eigenvalues of $\rho$.
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, Appendix, Theorem 5 eq. (A.3), p. 31

import Mathlib

open Matrix
open scoped ComplexOrder

namespace WallGSL

/-- Theorem 5 (appendix) of Wall (2013): a trace-preserving, identity-preserving, positive
linear map `T` on `n × n` complex matrices can only equalize the eigenvalues of a density
matrix `ρ`: for every `i`, the sum of any `i` eigenvalues of `T ρ` is at most the sum of
the `i` largest eigenvalues of `ρ`. -/
theorem unital_positive_map_eigenvalue_majorization
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hT_pos : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → (T A).PosSemidef)
    (hT_trace : ∀ A : Matrix (Fin n) (Fin n) ℂ, (T A).trace = A.trace)
    (hT_one : T 1 = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (i : ℕ) (s : Finset (Fin n)) (hs : s.card = i) :
    ∃ t : Finset (Fin n), t.card = i ∧
      ∑ j ∈ s, (hT_pos ρ hρ).isHermitian.eigenvalues j ≤ ∑ j ∈ t, hρ.isHermitian.eigenvalues j := by sorry

end WallGSL
