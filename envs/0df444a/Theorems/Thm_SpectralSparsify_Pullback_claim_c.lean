-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_claim_c
-- name    : SpectralSparsify.Pullback.claim_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:30.053978+00:00
-- url     : https://prove2.me/theorems/cd21103a-e0b3-4674-a958-93c33bb7ca8c
-- title:
--   Claim (c) — Ĩ = F̃ + G₁ is a (1 + 1/c)-approximation of G̃₀ + G₁
-- statement:
--   Under the hypotheses of Lemma 10.2 — $G=(V,E,w)$ a weighted graph on $n=|V|$ vertices, $\pi$ the map of a partition $V_1,\dots,V_k$, $G_0$ and $G_1$ the graphs of the edges between and inside the parts, $H$ the contraction of $G_0$, $0\le\epsilon<1/2$, $\widetilde H$ a $(1+\epsilon)$-approximation of $H$, $\widetilde G_0$ a pullback of $\widetilde H$ under $\pi$, $c\ge 3$, (1) each $V_i$ connected by edges of $G_1$, (2) every edge of $G_1$ of weight at least $c^2n^3$, (3) every edge of $G_0$ of weight $1$ — choose representatives $v_i\in V_i$ and let $\widetilde F$ be $\widetilde H$ placed on $\{v_1,\dots,v_k\}$ via $i\mapsto v_i$. Then
--   $$\widetilde I=\widetilde F+G_1\quad\text{is a }\Big(1+\frac1c\Big)\text{-approximation of } \widetilde G_0+G_1 .$$
--
--   This is claim (c) in the proof of Lemma 10.2: the pullback, together with the heavy edges, approximates the same graph $\widetilde I$ that approximates $G$.
--
--   **Formalization Note** $\widetilde H$ is \`zt\` with \`IsWGraph zt\`, and $\widetilde G_0$ is \`wt\` with \`IsWGraph wt\` and \`IsPullback wt zt π\` (which includes the condition, implicit in the paper, that every pullback edge joins two different parts). The paper leaves $\epsilon\ge 0$ implicit. The conclusion is \`IsApprox (1 + 1/c) (liftAlong r zt + intraPart w π) (wt + intraPart w π)\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, proof of Lemma 10.2, claim (c) (proof p. 38)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- Claim (c), proof of Lemma 10.2 (arXiv:0808.4134v3, pp. 37–38): if `H̃` is a
`(1 + ε)`-approximation of the contraction `H` of `G₀` and `G̃₀` is a pullback of `H̃` under `π`,
then `Ĩ = F̃ + G₁` is a `(1 + 1/c)`-approximation of `G̃₀ + G₁`, where `F̃` is `H̃` placed on the
representatives `r i ∈ Vᵢ`. Hypotheses 1–3 of Lemma 10.2, `0 ≤ ε < 1/2` and `c ≥ 3`. -/
theorem claim_c {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (ε c : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hc : 3 ≤ c)
    (zt : Fin k → Fin k → ℝ) (hzt : SpectralSparsify.Sampling.IsWGraph zt)
    (happrox : SpectralSparsify.Sampling.IsApprox (1 + ε) zt (contraction (crossPart w π) π))
    (wt : V → V → ℝ) (hwt : SpectralSparsify.Sampling.IsWGraph wt) (hpb : IsPullback wt zt π)
    (h1 : ∀ u v, π u = π v → (intraGraph w π).Reachable u v)
    (h2 : ∀ u v, π u = π v → w u v ≠ 0 → c ^ 2 * (Fintype.card V : ℝ) ^ 3 ≤ w u v)
    (h3 : ∀ u v, π u ≠ π v → w u v ≠ 0 → w u v = 1)
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) :
    SpectralSparsify.Sampling.IsApprox (1 + 1 / c) (liftAlong r zt + intraPart w π) (wt + intraPart w π) := by sorry

end SpectralSparsify.Pullback
