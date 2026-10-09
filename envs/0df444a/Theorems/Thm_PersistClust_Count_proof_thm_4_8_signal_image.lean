-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_signal_image
-- name    : PersistClust.Count.proof_thm_4_8_signal_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:15.739226+00:00
-- url     : https://prove2.me/theorems/5338d132-0af6-438e-8d48-607298e522d7
-- title:
--   Proof of Theorem 4.8, pp. 22–23, Regions III–V — γ(D₂) does not meet Δ^N_{d₁+2cδ} ∪ Λ^W_{d₁+2cδ}
-- statement:
--   Let $D$, $D'$, $\gamma$, $c,\delta>0$, $d_1\ge0$ and $d_2$ be as in the noise-image claim: $\gamma$ satisfies assertions (i)–(iv) of Theorem 4.5 with threshold and radius $c\delta$, $\delta<\frac{d_2-d_1}{5c}$, and $D$ is $(d_1,d_2)$-separated. Write $D_2$ for the points of $D$ in $\Delta^S_{d_2}\cap\Lambda^E_{d_2}$. Then
--   $$\gamma(D_2)\cap\big(\Delta^N_{d_1+2c\delta}\cup\Lambda^W_{d_1+2c\delta}\big)=\emptyset.$$
--
--   This is the analysis of Regions III, IV and V in the proof of the main theorem: the prominent peaks of $f$ are sent to points of high prominence and high birth.
--
--   **Formalization Note** The statement is abstract, with $D=D_0f$, $D'=D_0\mathcal R^f_\delta(L)$ in the main theorem; it covers every copy of every point of $D_2$.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), pp. 22–23, proof of Theorem 4.8, Regions III, IV and V

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

theorem proof_thm_4_8_signal_image
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂) :
    ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1), q.1 ∈ DeltaS d₂ ∩ LamE d₂ →
      pt (γ (Sum.inl ⟨q, hq⟩)) ∉ DeltaN (d₁ + 2 * c * δ) ∪ LamW (d₁ + 2 * c * δ) := by sorry

end PersistClust.Count
