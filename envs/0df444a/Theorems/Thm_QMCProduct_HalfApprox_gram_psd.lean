-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_gram_psd
-- name    : QMCProduct.HalfApprox.gram_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:21.184428+00:00
-- url     : https://prove2.me/theorems/f2a81d2d-3383-42f1-b810-2e2013a84fa0
-- title:
--   Section 4.3, p. 20 — the SWAP Gram matrix M(p, q, r) of a 2-positive pseudo-density is PSD
-- statement:
--   For a level-2 pseudo-density $\widetilde\rho$ and three distinct qubits $i,j,k$, set $p=s_{ij}$, $q=s_{ik}$, $r=s_{jk}$ and $t=(p+q+r-1)/2$. The real SWAP Gram matrix is
--   $$M=\begin{pmatrix}1&p&q&r\p&1&t&t\q&t&1&t\r&t&t&1\end{pmatrix}\succeq0.$$
--   This matrix packages the three adjacent edge values into the semidefinite constraint used by Lemma 8.
--
--   **Formalization Note** The four rows correspond to $I,S_{ij},S_{ik},S_{jk}$. All three sites are required to be distinct.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 20, Section 4.3, displayed matrix M

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Section 4.3, p. 20: the SWAP Gram matrix is positive semidefinite. -/
theorem gram_psd {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (swapGram (s ρt i j) (s ρt i k) (s ρt j k)).PosSemidef := by sorry

end QMCProduct.HalfApprox
