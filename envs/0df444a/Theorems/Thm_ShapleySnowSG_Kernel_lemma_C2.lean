-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_lemma_C2
-- name    : ShapleySnowSG.Kernel.lemma_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:42.0344+00:00
-- url     : https://prove2.me/theorems/127439d6-ac89-4370-b0a5-9433d035ab05
-- title:
--   Lemma C2, p. 31 — z ∈ S^M with kernel vectors yᵏ ≠ 0 gives z ∈ S^Δ and y¹ ⊗ ⋯ ⊗ yⁿ ∈ Ker(Δᵏ − zᵏΔ⁰)
-- statement:
--   Let $D=(M^k_\ell)$ be an $n\times(n+1)$ array of real square matrices, the matrices of row $k$ having a common size, with auxiliary matrices $\Delta^0,\dots,\Delta^n$. Let $z\in S^M$ and, for every $1\le k\le n$, let $y^k\neq0$ satisfy
--   $$(M^k_0+z^1M^k_1+\dots+z^nM^k_n)\,y^k=0 .$$
--   Then $z\in S^\Delta$ and
--   $$(\Delta^k-z^k\Delta^0)\,(y^1\otimes\dots\otimes y^n)=0\qquad\text{for all }1\le k\le n .$$
--
--   This is the bridge from the coupled multiparameter problem to the uncoupled one, and it produces the explicit kernel vector used in Proposition 2.4.4.
--
--   **Formalization Note** $z$ and the kernel vectors are complex, as in §2.4; the real input array is mapped into complex matrices. The tensor $y^1\otimes\dots\otimes y^n$ is the vector $(i_1,\dots,i_n)\mapsto\prod_k y^k_{i_k}$. The source prints "$M^k_0+z^1M^k+\dots+z^nM^k$"; it is read as $M^k_0+z^1M^k_1+\dots+z^nM^k_n$, as in its proof.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 31, Lemma C2

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP

namespace ShapleySnowSG.Kernel

open Matrix

/-- Lemma C2, p. 31: for an `n × (n+1)` array of real square matrices, let `z ∈ S^M ⊆ ℂⁿ` and
`y^k ≠ 0` in `Ker(M^k_0 + z^1 M^k_1 + ⋯ + z^n M^k_n)` for all `k`. Then `z ∈ S^Δ` and
`y^1 ⊗ ⋯ ⊗ y^n ∈ Ker(Δ^k − z^k Δ^0)` for all `k`. -/
theorem lemma_C2 {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ)
    (z : Fin n → ℂ) (hz : z ∈ SM (complexArray M))
    (y : ∀ k, p k → ℂ) (hy0 : ∀ k, y k ≠ 0)
    (hy : ∀ k, pencil (complexArray M) z k *ᵥ y k = 0) :
    z ∈ SDelta (complexArray M) ∧ ∀ k,
      (aux (complexArray M) k.succ - z k • aux (complexArray M) 0) *ᵥ tensorVec y = 0 := by sorry

end ShapleySnowSG.Kernel
