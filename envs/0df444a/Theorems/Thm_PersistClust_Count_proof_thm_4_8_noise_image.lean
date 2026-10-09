-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_noise_image
-- name    : PersistClust.Count.proof_thm_4_8_noise_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:48.025223+00:00
-- url     : https://prove2.me/theorems/aad360ae-7311-4baa-ad37-4abb174b809b
-- title:
--   Proof of Theorem 4.8, p. 22, Regions I–II — γ(D₁) ⊆ Δ^N_{d₁+2cδ} ∪ Λ^W_{d₁+2cδ}
-- statement:
--   Let $D$ and $D'$ be two diagrams (multisets of off-diagonal points of $\overline{\mathbb R}^2$ with birth $>$ death, plus the diagonal with infinite multiplicity), and let $\gamma$ be a multi-bijection between them satisfying assertions (i)–(iv) of Theorem 4.5 with threshold $\alpha=c\delta$ and radius $c\delta$, where $c,\delta>0$. Let $d_1\ge0$ and $d_2$ satisfy $\delta<\frac{d_2-d_1}{5c}$, and assume $D$ is $(d_1,d_2)$-separated. Write $D_1$ for the points of $D$ in $\Delta^N_{d_1}$. Then
--   $$\gamma(D_1)\subseteq\Delta^N_{d_1+2c\delta}\cup\Lambda^W_{d_1+2c\delta}.$$
--
--   This is the analysis of Regions I and II in the proof of the main theorem: the noise points of $D_0f$ are sent to points of low prominence or low birth.
--
--   **Formalization Note** The statement is abstract: in the main theorem, $D=D_0f$, $D'=D_0\mathcal R^f_\delta(L)$ and $\gamma$ comes from Theorem 4.5 with $\alpha=c\delta$. Every copy of a point of $D_1$ is covered, and the image may be a diagonal copy.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 22, proof of Theorem 4.8, Regions I and II

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

theorem proof_thm_4_8_noise_image
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂) :
    ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1), q.1 ∈ DeltaN d₁ →
      pt (γ (Sum.inl ⟨q, hq⟩)) ∈ DeltaN (d₁ + 2 * c * δ) ∪ LamW (d₁ + 2 * c * δ) := by sorry

end PersistClust.Count
