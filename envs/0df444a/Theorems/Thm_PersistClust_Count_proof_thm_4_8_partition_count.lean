-- Prove2me | Theorems.Thm_PersistClust_Count_proof_thm_4_8_partition_count
-- name    : PersistClust.Count.proof_thm_4_8_partition_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:08.640979+00:00
-- url     : https://prove2.me/theorems/15c3e84c-21c0-498c-98e2-679cb5d06242
-- title:
--   Proof of Theorem 4.8, p. 23 — for τ ∈ (d₁+2cδ, d₂−3cδ), D′ has as many points in Δ^S_τ ∩ Λ^E_τ as D has in Δ^S_{d₂}
-- statement:
--   Let $D$, $D'$, $\gamma$, $c,\delta>0$, $d_1\ge0$ and $d_2$ be as in the noise-image claim: $\gamma$ satisfies assertions (i)–(iv) of Theorem 4.5 with threshold and radius $c\delta$, $\delta<\frac{d_2-d_1}{5c}$, and $D$ is $(d_1,d_2)$-separated. Then for every threshold $\tau$ with $d_1+2c\delta<\tau<d_2-3c\delta$, the total multiplicity of $D'$ in the region $\Delta^S_\tau\cap\Lambda^E_\tau$ equals the total multiplicity of $D$ in $\Delta^S_{d_2}$:
--   $$\#\big(D'\cap\Delta^S_\tau\cap\Lambda^E_\tau\big)=\#\big(D\cap\Delta^S_{d_2}\big),$$
--   multiplicities counted, in $\mathbb N\cup\{+\infty\}$; the right-hand side is the number of peaks of prominence at least $d_2$.
--
--   This is the counting step of the main theorem: the threshold $\tau$ separates the images of the signal points from everything else in $D'$.
--
--   **Formalization Note** The left-hand side counts all off-diagonal points of $D'$ in the region, not only images of off-diagonal points of $D$: points of $D'$ matched with diagonal copies of $D$ must also be shown to lie outside the region (the paper's "is partitioned into" passes over them). The equality holds in $\mathbb N\cup\{+\infty\}$ with no finiteness assumption; in the source, $D_0f$ is tame, so both counts are finite (the page's "same (finite) total multiplicity").
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 23, proof of Theorem 4.8, the partition of D₀𝓡^f_δ(L) and the equality of total multiplicities

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

theorem proof_thm_4_8_partition_count
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard
      = prominentCount D d₂ := by sorry

end PersistClust.Count
