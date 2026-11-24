-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_lemma_4_12
-- name    : RobustPMI.Hierarchy.Supplement.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:43:46.163187+00:00
-- url     : https://prove2.me/theorems/d6df34e6-d272-4a94-b3ed-0c32f0b7d55b
-- title:
--   Lemma 4.12, p. 22 — under a ball constraint, f − λ − 𝓛_S(P) lies in the interior of 𝒬_k(Θ)
-- statement:
--   Suppose Assumption 4(i) holds: $\theta_1(y)=b^2-\sum_{i=1}^\ell y_i^2$ for some $b\ne0$. Then for every $k\ge\max\{\lceil k_x/2\rceil,\lceil k_y/2\rceil\}$ and every $S\in\mathcal M^m_k(G)$ there exists $\lambda\in\mathbb R$ such that
--   $$f(y)-\lambda-\mathscr L_S(P(y,x))\in\mathcal Q^\circ_k(\Theta),$$
--   where $\mathcal Q^\circ_k(\Theta)$ is the interior of the truncated quadratic module $\mathcal Q_k(\Theta)$ in the space $\mathbb R[y]_{2k}$ of polynomials of degree at most $2k$.
--
--   The lemma provides the strict feasibility used to rule out a duality gap in Theorem 4.14.
--
--   **Formalization Note** $\mathbb R[y]_{2k}$ is identified with its coefficient space $\mathbb R^{\mathbb N^\ell_{2k}}$ (any norm gives the same interior); the statement also records that the polynomial has degree at most $2k$.
--
--   Differences from the source:
--   - encoding: interior of 𝒬_k(Θ) → interior of the image of 𝒬_k(Θ) ∩ ℝ[y]_{2k} under the coefficient map ℝ[y]_{2k} → ℝ^{ℕ^ℓ_{2k}}, plus deg ≤ 2k; reason: the coefficient map is a linear isomorphism of ℝ[y]_{2k}, the space the interior lives in
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 22, Lemma 4.12

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Lemma 4.12 (p. 22): under Assumption 4 (i), for every `k ≥ max{⌈k_x/2⌉, ⌈k_y/2⌉}` and every
`S ∈ 𝓜^m_k(G)` there is `λ ∈ ℝ` with `f(y) − λ − 𝓛_S(P(y, x)) ∈ 𝒬°_k(Θ)`, the interior of
`𝒬_k(Θ)` in the space `ℝ[y]_{2k}`. -/
theorem lemma_4_12 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm) (h4 : Assumption4i θ)
    (k : ℕ) (hkx : (kx P G + 1) / 2 ≤ k) (hky : (ky f θ P + 1) / 2 ≤ k)
    (S : MatSeq (Fin n) (Fin m)) (hS : S ∈ MM k G) :
    ∃ lam : ℝ, InInteriorQTheta k θ (f - C lam - rieszP S P) := by sorry

end RobustPMI.Hierarchy.Supplement
