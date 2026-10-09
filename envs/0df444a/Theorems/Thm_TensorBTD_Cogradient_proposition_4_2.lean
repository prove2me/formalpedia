-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_proposition_4_2
-- name    : TensorBTD.Cogradient.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:56.550637+00:00
-- url     : https://prove2.me/theorems/1190d262-aa19-4265-ab64-504965d7bf45
-- title:
--   Proposition 4.2, p. 7 — V = A^(p_1) ⊙ ⋯ ⊙ A^(p_N) satisfies VᴴV = ∗ₙ A^(n)ᴴA^(n)
-- statement:
--   Let $A^{(n)}\in\mathbb C^{I_n\times J}$ for $n=1,\dots,N$, let $p$ be any permutation of $\{1,\dots,N\}$, and let
--   $$V=A^{(p_1)}\odot\cdots\odot A^{(p_N)}$$
--   be the Khatri–Rao product of the matrices in the order $p$. Let $W=\ast_{n=1}^N A^{(n)\mathrm H}A^{(n)}$ be the Hadamard (entrywise) product of all the Gramians $A^{(n)\mathrm H}A^{(n)}$. Then
--   $$V^{\mathrm H}V=W .$$
--
--   This is the standard identity that turns the Gramian of a Khatri–Rao product into a Hadamard product of small $J\times J$ Gramians; it is the reason the cogradient of Theorem 4.4 can be evaluated without forming $V$.
--
--   **Formalization Note.** The rows of $V$ are indexed by the tuple $(i_{p_1},\dots,i_{p_N})$ rather than by an integer; the entry in row $(i_{p_1},\dots,i_{p_N})$ and column $j$ is $\prod_k a^{(p_k)}_{i_{p_k}j}$. Columns are 0-based. For $N=0$ both sides are the all-ones matrix (empty products).
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 7, Proposition 4.2

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Proposition 4.2, p. 7: for matrices `A^(n) ∈ ℂ^{I_n × J}`, `n = 1, …, N`, and any permutation
`p` of the modes, the Khatri–Rao string `V = A^(p_1) ⊙ ⋯ ⊙ A^(p_N)` satisfies `Vᴴ V = W`, where
`W = ∗_n A^(n)ᴴ A^(n)` is the Hadamard product of the Gramians. -/
theorem proposition_4_2 {N J : ℕ} {I : Fin N → ℕ} (A : (n : Fin N) → Matrix (Fin (I n)) (Fin J) ℂ)
    (p : Equiv.Perm (Fin N)) :
    (krString A p)ᴴ * krString A p = Matrix.of fun j j' => ∏ n, ((A n)ᴴ * A n) j j' := by sorry

end TensorBTD.Cogradient
