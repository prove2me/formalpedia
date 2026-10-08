-- Prove2me | Theorems.Thm_SpectralSparsify_Pullback_claim_b
-- name    : SpectralSparsify.Pullback.claim_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:28.387866+00:00
-- url     : https://prove2.me/theorems/32def300-0ba3-40cb-8e39-c5dc6d0edc3c
-- title:
--   Claim (b) — Ĩ = F̃ + G₁ is a (1 + ε)-approximation of I = F + G₁
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph, $\pi$ the map of a partition $V_1,\dots,V_k$, $G_0$ and $G_1$ the graphs of the edges between and inside the parts, and $H$ the contraction of $G_0$ under $\pi$. Let $0\le\epsilon<1/2$ and let $\widetilde H$ be a $(1+\epsilon)$-approximation of $H$. Choose representatives $v_i\in V_i$ and let $F$, $\widetilde F$ be $H$, $\widetilde H$ placed on $\{v_1,\dots,v_k\}$ via $i\mapsto v_i$. Then
--   $$\widetilde I=\widetilde F+G_1\quad\text{is a }(1+\epsilon)\text{-approximation of } I=F+G_1 .$$
--
--   This is claim (b) in the proof of Lemma 10.2.
--
--   **Formalization Note** The paper leaves implicit that $\epsilon\ge 0$; it is a hypothesis here, as in Lemma 10.2. The conclusion is \`IsApprox (1 + ε) (liftAlong r zt + intraPart w π) (liftAlong r (contraction (crossPart w π) π) + intraPart w π)\`.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, p. 37, proof of Lemma 10.2, claim (b) (proof p. 38)

import Mathlib
import Definitions.Def_SpectralSparsify_Pullback_WeightedGraph
import Definitions.Def_SpectralSparsify_Pullback_Contraction

namespace SpectralSparsify.Pullback

/-- Claim (b), proof of Lemma 10.2 (arXiv:0808.4134v3, p. 37): if `H̃` is a `(1 + ε)`-approximation
of the contraction `H` of `G₀`, then `Ĩ = F̃ + G₁` is a `(1 + ε)`-approximation of `I = F + G₁`,
where `F`, `F̃` are `H`, `H̃` placed on the representatives `r i ∈ Vᵢ`. -/
theorem claim_b {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → V → ℝ) (hw : SpectralSparsify.Sampling.IsWGraph w) (π : V → Fin k) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (zt : Fin k → Fin k → ℝ) (hzt : SpectralSparsify.Sampling.IsWGraph zt)
    (happrox : SpectralSparsify.Sampling.IsApprox (1 + ε) zt (contraction (crossPart w π) π))
    (r : Fin k → V) (hr : ∀ i, π (r i) = i) :
    SpectralSparsify.Sampling.IsApprox (1 + ε) (liftAlong r zt + intraPart w π)
      (liftAlong r (contraction (crossPart w π) π) + intraPart w π) := by sorry

end SpectralSparsify.Pullback
