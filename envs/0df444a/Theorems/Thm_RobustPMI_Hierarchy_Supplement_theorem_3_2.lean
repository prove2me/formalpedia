-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_3_2
-- name    : RobustPMI.Hierarchy.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:42:03.812662+00:00
-- url     : https://prove2.me/theorems/54251882-d3b6-44ba-ac29-0f0dc97441bc
-- title:
--   Theorem 3.2, p. 10 (corrected: d_G ≥ 1 for (ii) ⇒ (i)) — truncated matrix-valued 𝒳-moment problem via flat extensions
-- statement:
--   Let $G\in\mathbb S[x]^q$ and $\mathcal X=\{x\in\mathbb R^n:G(x)\succeq0\}$, $d_G=\lceil\deg G/2\rceil$. Let $S=(S_\alpha)_{\alpha\in\mathbb N^n_{2k}}$ be a truncated sequence of symmetric $m\times m$ matrices, with moment matrix $M_k(S)$ and localizing matrix $M_k(GS)$. Consider:
--
--   1. $S$ admits an atomic representing measure $\Phi=\sum_{i=1}^rW_i\delta_{x^{(i)}}$ with $W_i\in\mathbb S^m_+$, $x^{(i)}\in\mathcal X$ and $\sum_{i=1}^r\operatorname{rank}W_i=\operatorname{rank}M_k(S)$;
--   2. $M_k(S)\succeq0$ and $S$ admits an extension $\tilde S=(\tilde S_\alpha)_{\alpha\in\mathbb N^n_{2(k+d_G)}}$ with
--   $$M_{k+d_G}(\tilde S)\succeq0,\qquad M_k(G\tilde S)\succeq0,\qquad \operatorname{rank}M_k(S)=\operatorname{rank}M_{k+d_G}(\tilde S).$$
--
--   Then (1) implies (2), and if $d_G\ge1$, (2) implies (1).
--
--   This solves the truncated matrix-valued $\mathcal X$-moment problem and is the tool behind every extraction result of the paper (Theorems 4.11, 4.18, 4.21, 5.4).
--
--   **Formalization Note** The representing measure is a finitely atomic PSD measure on $\mathcal X$ with distinct atoms; "represents" means $S_\alpha=\sum_iW_i(x^{(i)})^\alpha$ for every $|\alpha|\le2k$.
--
--   Differences from the source:
--   - correction: (ii) ⇒ (i) for every G → (ii) ⇒ (i) under the additional premise 1 ≤ d_G; reason: for constant G (d_G = 0) the rank condition is empty and the implication fails: G ≡ 1, n = m = 1, k = 2, S = (1, 0, 0, 0, 1) has M_2(S) ⪰ 0 and no representing measure; the proof uses Theorem 3.1, which needs an extension by one degree
--   - encoding: truncated sequence S = (S_α)_{α∈ℕⁿ_{2k}} ⊆ 𝕊^m → a total sequence S with S_α symmetric for |α| ≤ 2k, of which only |α| ≤ 2k is read; the atoms of Φ are distinct; reason: same instances; entries beyond 2k are never read
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 10, Theorem 3.2

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 3.2 (p. 10): for a truncated sequence `S = (S_α)_{α ∈ ℕⁿ_{2k}} ⊆ 𝕊^m`, consider
(i) `S` admits an atomic representing measure `Φ = ∑_{i=1}^r W_i δ_{x^{(i)}}` with `W_i ∈ 𝕊^m_+`,
`x^{(i)} ∈ 𝒳` and `∑_i rank(W_i) = rank(M_k(S))`;
(ii) `M_k(S) ⪰ 0` and `S` admits an extension `S̃ = (S̃_α)_{α ∈ ℕⁿ_{2(k+d_G)}}` with
`M_{k+d_G}(S̃) ⪰ 0`, `M_k(G S̃) ⪰ 0` and `rank(M_k(S)) = rank(M_{k+d_G}(S̃))`.
Then (i) ⇒ (ii), and (ii) ⇒ (i) when `d_G ≥ 1` (for constant `G` the rank condition is empty and
the implication fails). -/
theorem theorem_3_2 {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hG : G.IsSymm) (k : ℕ) (S : MatSeq (Fin n) (Fin m))
    (hS : ∀ α ∈ monos (σ := Fin n) (2 * k), (S α).IsSymm) :
    ((∃ μ : AtomicMeasure m G, Represents μ k S ∧ ∑ i, (μ.W i).rank = (momentMat k S).rank) →
      (momentMat k S).PosSemidef ∧
        ∃ St : MatSeq (Fin n) (Fin m), (∀ α ∈ monos (σ := Fin n) (2 * k), St α = S α) ∧
          (momentMat (k + dG G) St).PosSemidef ∧ (locMat k G St).PosSemidef ∧
          (momentMat k S).rank = (momentMat (k + dG G) St).rank) ∧
    (1 ≤ dG G →
      ((momentMat k S).PosSemidef ∧
        ∃ St : MatSeq (Fin n) (Fin m), (∀ α ∈ monos (σ := Fin n) (2 * k), St α = S α) ∧
          (momentMat (k + dG G) St).PosSemidef ∧ (locMat k G St).PosSemidef ∧
          (momentMat k S).rank = (momentMat (k + dG G) St).rank) →
      ∃ μ : AtomicMeasure m G, Represents μ k S ∧ ∑ i, (μ.W i).rank = (momentMat k S).rank) := by sorry

end RobustPMI.Hierarchy.Supplement
