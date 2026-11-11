-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_6_2
-- name    : RobustCorrClust.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:39:37.36122+00:00
-- url     : https://prove2.me/theorems/76549ea6-d5fa-412e-8da2-07786369fe3f
-- title:
--   Lemma 6.2 — cost transfer: cost_G(C) ≤ cost_Q(C) + |E⁺_G △ E⁺_Q|, and in expectation for a β-approximate randomized output
-- statement:
--   Let $G$ and $Q$ be complete signed graphs on the same $n$ vertices. Then
--
--   1. for every clustering $\mathcal C$, $\mathrm{cost}_G(\mathcal C)\le\mathrm{cost}_Q(\mathcal C)+|E^+_G\triangle E^+_Q|$;
--   2. let $\mathcal C^*$ be an optimal clustering of $G$ and $\beta\ge0$. If a randomized algorithm on $Q$ returns a clustering $\mathcal C_Q$ with $\mathbb E[\mathrm{cost}_Q(\mathcal C_Q)]\le\beta\,\mathrm{OPT}(Q)$ (a $\beta$-approximation on $Q$), then
--   $$\mathbb E[\mathrm{cost}_G(\mathcal C_Q)]\le\beta\,\mathrm{cost}_Q(\mathcal C^*)+|E^+_G\triangle E^+_Q| ,$$
--   the expectation over the algorithm's randomness for this fixed $Q$.
--
--   The law of $\mathcal C_Q$ is a probability vector $\mu$ on labelings $\ell:\{0,\dots,n-1\}\to\{0,\dots,n-1\}$, the clustering of $\ell$ putting $u,v$ together iff $\ell(u)=\ell(v)$.
--
--   Differences from the source:
--   - generalization: a $\beta$-approximation algorithm (ratio $\beta\ge1$) → any $\beta\ge0$ with $\mathbb E[\mathrm{cost}_Q]\le\beta\,\mathrm{OPT}(Q)$; reason: an approximation ratio is at least $1$, so the source's case is included.
--   - encoding: the output distribution of the algorithm → a probability vector on labelings into $\{0,\dots,n-1\}$; reason: every partition of $n$ vertices has such a labeling, so every distribution on clusterings is one.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 44, Lemma 6.2

import Mathlib
import Definitions.Def_RobustCorrClust_Main_SignedGraph

namespace RobustCorrClust.Main

/-- Lemma 6.2 (p. 44), both parts: (i) `cost_G(C) ≤ cost_Q(C) + |E⁺_G △ E⁺_Q|` for every
clustering `C`; (ii) if a randomized algorithm on `Q` returns a clustering distributed as `μ`
(a probability distribution on labelings `ℓ : Fin n → Fin n`, clustering = equal labels) with
`E_μ[cost_Q] ≤ β OPT(Q)`, and `C*` is an optimal clustering of `G`, then
`E_μ[cost_G] ≤ β cost_Q(C*) + |E⁺_G △ E⁺_Q|`. -/
theorem lemma_6_2 {n : ℕ} (G Q : SimpleGraph (Fin n)) :
    (∀ D : Setoid (Fin n), cost G D ≤ cost Q D + symmDiffCount G Q) ∧
    ∀ (β : ℝ) (μ : (Fin n → Fin n) → ℝ) (Cstar : Setoid (Fin n)),
      0 ≤ β → IsOptimal G Cstar → (∀ ℓ, 0 ≤ μ ℓ) → ∑ ℓ, μ ℓ = 1 →
      ∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ) ≤ β * (OPT Q : ℝ) →
      ∑ ℓ, μ ℓ * (cost G (Setoid.ker ℓ) : ℝ) ≤
        β * (cost Q Cstar : ℝ) + (symmDiffCount G Q : ℝ) := by sorry

end RobustCorrClust.Main
