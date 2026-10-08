-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_theorem_6_5_core
-- name    : TensorNP.SpectralNorm.theorem_6_5_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:42.286087+00:00
-- url     : https://prove2.me/theorems/3fc57aa4-966d-421a-abbc-ec33383caa45
-- title:
--   Theorems 6.5 and 1.10 (core) — ω(G) is the unique l with ‖A_l‖₂,₂,₂ = 1, and the largest l for which 1 is a singular value of A_l
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with clique number $\omega=\omega(G)$, and enumerate its $e$ edges in any order. For each positive integer $l$ let $\mathcal A_l\in\mathbb Q^{v\times v\times(l+2e)}$ be the tensor whose entry $a_{ijk}$ is the coefficient of $u_iv_jw_k$ in the multilinear form
--   $$
--   \sum_{i=1}^l\Big(\mathbf u^\top\tfrac1lI\mathbf v\Big)w_i+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{l+k}+\sum_{k=1}^e(\mathbf u^\top E_k\mathbf v)w_{e+l+k},
--   $$
--   with $E_k=\frac12E_{i_kj_k}+\frac12E_{j_ki_k}$ for the $k$-th edge $\{i_k,j_k\}$. Regarding $\mathcal A_l$ as a real tensor:
--
--   1. for every $l\ge1$, $\|\mathcal A_l\|_{2,2,2}=1$ if and only if $l=\omega$;
--   2. $1$ is a unit $\ell^2$-singular value of $\mathcal A_\omega$;
--   3. for every $l>\omega$, $1$ is not a unit $\ell^2$-singular value of $\mathcal A_l$;
--   4. hence $\omega$ is the largest $l\in\{1,\dots,v\}$ for which $1$ is a unit $\ell^2$-singular value of $\mathcal A_l$.
--
--   This is the mathematical core of the paper's polynomial-time Turing reductions from the clique number to the tensor singular value problem (Theorem 6.5, $\sigma=1$) and to the spectral norm problem (Theorem 1.10, $\sigma=1$): querying an oracle for $l=1,\dots,v$ determines $\omega(G)$. A general fixed $0\neq\sigma\in\mathbb Q$ is handled by scaling $\mathcal A_l$ by $\sigma$.
--
--   **Formalization Note** This is not an NP-hardness statement. The polynomial size of $\mathcal A_l$, the $v$-query procedure and the NP-completeness of deciding $\omega(G)\ge l$ (Karp 1972, cited by the paper) are not formalized, and neither is the scaling to general $\sigma$. Singular values are taken with unit singular vectors (Definition 6.1 has no normalization; unnormalized, every nonzero number would be a singular value of $\mathcal A_l$ and clause 3 would be false). The paper does not claim, and this statement does not assert, that $1$ fails to be a singular value of $\mathcal A_l$ for $l<\omega$. The tensor is defined for any enumeration `ε : Fin e ≃ G.edgeSet` of the edges and the statement holds for each one; the third block of $\mathbf w$ uses the index $w_{e+l+k}$ of the proof of Lemma 6.11 (its statement prints $w_{m+l+k}$).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:22, Theorem 6.5; p. 0:9, Theorem 1.10; p. 0:24, proofs of Theorems 6.5 and 1.10

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor

namespace TensorNP.SpectralNorm

/-- **Theorems 6.5 and 1.10, encoding-free core.** Let `G` be a simple graph on `v ≥ 1` vertices
with clique number `ω = ω(G)`, and `ε` any enumeration of its `e` edges. For the rational tensors
`A_l` (read over ℝ):
(a) for every `l ≥ 1`, `‖A_l‖_{2,2,2} = 1` iff `l = ω`;
(b) `1` is a unit ℓ²-singular value of `A_ω`;
(c) for every `l > ω`, `1` is not a unit ℓ²-singular value of `A_l`;
(d) hence `ω` is the largest `l ∈ {1, …, v}` for which `1` is a unit ℓ²-singular value of
`A_l`. -/
theorem theorem_6_5_core {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) :
    (∀ l : ℕ, 1 ≤ l →
        (specNorm (fun i j k => (cliqueTensor G ε l i j k : ℝ)) = 1 ↔ l = G.cliqueNum)) ∧
      IsUnitSingularValue (fun i j k => (cliqueTensor G ε G.cliqueNum i j k : ℝ)) 1 ∧
      (∀ l : ℕ, G.cliqueNum < l →
        ¬ IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) 1) ∧
      IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧
          IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) 1}
        G.cliqueNum := by sorry

end TensorNP.SpectralNorm
