-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_claim_a
-- name    : SpectralSparsify.Pullback.claim_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:34.004293+00:00
-- url     : https://prove2.me/theorems/4d70ae2e-5155-4a10-b6fb-f7e989318eb9
-- title:
--   Claim (a) — I = F + G₁ is a (1 + 1/c)-approximation of G
-- statement:
--   Under the hypotheses of Lemma 10.2 on $G$ — $G=(V,E,w)$ a weighted graph on $n=|V|$ vertices, $\pi$ the map of a partition $V_1,\dots,V_k$, $G_0$ and $G_1$ the graphs of the edges between and inside the parts, $c\ge 3$, (1) each $V_i$ connected by edges of $G_1$, (2) every edge of $G_1$ of weight at least $c^2n^3$, (3) every edge of $G_0$ of weight $1$ — choose representatives $v_i\in V_i$ and let $F$ be the contraction $H$ of $G_0$ placed on $\{v_1,\dots,v_k\}$ via $i\mapsto v_i$. Then
--   $$I = F + G_1\quad\text{is a }\Big(1+\frac1c\Big)\text{-approximation of } G .$$
--
--   This is claim (a) in the proof of Lemma 10.2: once the heavy intra-part edges are kept, the light edges between parts may be replaced by the contracted graph sitting on one vertex per part.
--
--   **Formalization Note** The conclusion is \`IsApprox (1 + 1/c) (liftAlong r (contraction (crossPart w π) π) + intraPart w π) w\`, for any representatives \`r\` with \`π (r i) = i\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, proof of Lemma 10.2, claim (a) (proof p. 38)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- Claim (a), proof of Lemma 10.2 (arXiv:0808.4134v3, p. 37): `I = F + G₁` is a
`(1 + 1/c)`-approximation of `G`, where `F` is the contraction `H` of `G₀` placed on the
representatives `r i ∈ Vᵢ`. Hypotheses 1–3 of Lemma 10.2 and `c ≥ 3`. -/
theorem claim_a {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (c : ℝ) (hc : 3 ≤ c)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1)
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) :
    SpectralSparsify.Sampling.IsApprox (1 + 1 / c) (liftAlong r (contraction (crossPart w π) π) + intraPart w π) w := by sorry

end SpectralSparsify.Pullback
