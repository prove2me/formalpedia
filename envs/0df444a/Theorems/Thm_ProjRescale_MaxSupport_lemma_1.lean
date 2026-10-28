-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_lemma_1
-- name    : ProjRescale.MaxSupport.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:26.49093+00:00
-- url     : https://prove2.me/theorems/3a8e9170-f279-4ba4-8ab0-4adc219a03aa
-- title:
--   Lemma 1, pp. 5–6 — a basic-procedure certificate z gives x_i ≤ ‖x‖∞/2 on L ∩ ℝⁿ₊, and σ_i(DL) = 2σ_i(L), σ_j(DL) = σ_j(L) for D = I + e_ie_iᵀ
-- statement:
--   Let $L \subseteq \mathbb R^n$ be a linear subspace and $P$ the orthogonal projection onto $L$. Suppose $z \in \mathbb R^n_+ \setminus \{0\}$ and $i \in \{1,\dots,n\}$ satisfy
--
--   $$\|(Pz)^+\|_1 \le \tfrac12 \|z\|_\infty = \tfrac12 z_i .$$
--
--   Then
--
--   1. every $x \in L \cap \mathbb R^n_+$ satisfies $x_i \le \|x\|_\infty / 2$ (equation (4));
--   2. for $D = I + e_i e_i^{\mathsf T}$ (the diagonal matrix with $D_{ii} = 2$ and all other diagonal entries $1$), the rescaled subspace $DL$ satisfies $\sigma_i(DL) = 2\sigma_i(L)$;
--   3. $\sigma_j(DL) = \sigma_j(L)$ for every $j \neq i$.
--
--   Here $\sigma_j(L) = \max\{x_j : x \in L\cap\mathbb R^n_+,\ \|x\|_\infty\le 1\}$ and $(v)^+$ is the positive part of $v$. This lemma is the quantitative effect of one rescaling step of Algorithm 1: a certificate returned by the basic procedure doubles the condition coordinate $\sigma_i$ and leaves the others unchanged.
--
--   **Formalization Note** $P$ is Mathlib's orthogonal projection onto $L$ viewed as a map $\mathbb R^n \to \mathbb R^n$; $\|\cdot\|_\infty$ and $\|(\cdot)^+\|_1$ are written coordinatewise, and the hypothesis "$\|z\|_\infty = z_i$" is stated literally.
--
--   Differences from the source: none.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, pp. 5–6, Lemma 1 (Equation (4))

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

/-- Lemma 1, pp. 5–6. Let `P` be the orthogonal projection onto `L`, and let `z ∈ ℝⁿ₊ \ {0}` satisfy
`‖(Pz)⁺‖₁ ≤ ½‖z‖∞ = ½z_i`. Then every `x ∈ L ∩ ℝⁿ₊` has `x_i ≤ ‖x‖∞/2` (4), and for
`D = I + e_i e_iᵀ` the rescaled subspace satisfies `σ_i(DL) = 2σ_i(L)` and `σ_j(DL) = σ_j(L)` for
`j ≠ i`. -/
theorem lemma_1 {n : ℕ} (L : Submodule ℝ (E n)) (z : E n) (i : Fin n)
    (hz : z ∈ nonneg n) (hz0 : z ≠ 0) (hzi : supNorm z = z i)
    (hP : posL1 (L.starProjection z) ≤ supNorm z / 2) :
    (∀ x ∈ L, x ∈ nonneg n → x i ≤ supNorm x / 2) ∧
      sigmaI (diagScale (Function.update (fun _ => 1) i 2) L) i = 2 * sigmaI L i ∧
      ∀ j, j ≠ i → sigmaI (diagScale (Function.update (fun _ => 1) i 2) L) j = sigmaI L j := by sorry

end ProjRescale.MaxSupport
