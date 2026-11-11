-- Prove2me | Theorems.Thm_RamseyLST_Main_theorem_25
-- name    : RamseyLST.Main.theorem_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:15.206244+00:00
-- url     : https://prove2.me/theorems/cf004ad9-f8d5-4ea5-9ebe-254fb129f872
-- title:
--   Theorem 25 — existence form, as invoked in the proof of Theorem 1: weighted strong $(Ct, 1 - c(\log t+\log\log(4\Phi))/t, C_D)$-Ramsey spanning trees
-- statement:
--   There are absolute constants $t_0$, $C\ge1$, $C_D\ge1$ and $c>0$ such that the following holds for every real $t\ge t_0$. Let $G=(V,E,\ell)$ be a finite connected weighted graph, let $Z^{in}\subseteq V$ be a candidate core with aspect ratio $\Phi=\Phi_G(Z^{in})$, and let $w:Z^{in}\to\mathbb R_{\ge0}$ be a weight function. Then $G$ has a weighted strong
--
--   $$\Big(C\,t,\ \max\Big(0,\ 1-c\,\frac{\log t+\log\log(4\Phi)}{t}\Big),\ C_D\Big)\text{-Ramsey spanning tree}$$
--
--   with respect to $w$ (logarithms in base 2). That is, there are a spanning tree $T$ and a core $Z\subseteq Z^{in}$ with $\sum_{z\in Z}w(z)^{\psi}\ge w(Z^{in})^{\psi}$ when $Z^{in}\neq\emptyset$ (for the exponent $\psi$ above), $d_T(z,v)\le Ct\,d_G(z,v)$ for every $z\in Z$ and $v\in V$, and $\operatorname{diam}(T)\le C_D\operatorname{diam}(G)$.
--
--   This is the bounded-aspect-ratio case: in the words of the proof of Theorem 1 (p. 58), HierarchicalPetDec with parameter $t$ satisfies Assumption 1 strongly with $\alpha_0=Ct$ and $\psi(\Phi)=1-c(\log t+\log\log(4\Phi))/t$.
--
--   Differences from the source:
--   - reading: it is possible to find in polynomial time a … Ramsey spanning tree → there exists such a Ramsey spanning tree; reason: the item is the existence form the paper itself states on p. 58; the paper fixes no computational model, so the running-time clause is not part of the item
--   - encoding: O(t), C_D, 1 − O((log t + log log(4Φ))/t), t ≥ t_0 → explicit constants t₀, C ≥ 1, C_D ≥ 1, c > 0 chosen before t, G, Z^in and w (as on p. 58); reason: explicit constants for O(·)
--   - reading: core exponent 1 − c(log t + log log(4Φ))/t → max(0, 1 − c(log t + log log(4Φ))/t); reason: p. 10: an exponent stated without a lower bound is read as its maximum with 0; this makes ψ a map [1, ∞) → [0, 1] as Assumption 1 requires
--   - reading: t ≥ t_0 → every real t ≥ t₀; reason: the proof of Theorem 1 uses t = α/(2C), which is not an integer; the real reading is the stronger one
--   - encoding: weighted core size requirement for Z^in = ∅ → imposed only for non-empty Z^in; reason: p. 56: for an empty candidate core 'the weighted core size requirement holds trivially with an empty core'; Real.rpow would make 0 ≥ 0^0 = 1 false
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 33 (PDF 37), Theorem 25, in the existence form stated in the proof of Theorem 1, p. 58 (PDF 62)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_RamseySpanningTree

open ARTreeCover

namespace RamseyLST.Main

/-- Theorem 25 (p. 33), in the existence form invoked in the proof of Theorem 1 (p. 58): there
are absolute constants `t₀`, `C ≥ 1`, `C_D ≥ 1` and `c > 0` such that for every real `t ≥ t₀`,
every finite connected weighted graph `G`, every candidate core `Zin ⊆ V` with aspect ratio
`Φ = Φ_G(Zin)` and every weight function `w : Zin → ℝ_{≥0}`, `G` has a weighted strong
`(C t, max(0, 1 − c (log t + log log(4Φ))/t), C_D)`-Ramsey spanning tree with respect to `w`. -/
theorem theorem_25 :
    ∃ t₀ C CD c : ℝ, 1 ≤ C ∧ 1 ≤ CD ∧ 0 < c ∧
      ∀ t : ℝ, t₀ ≤ t →
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.graph.Connected →
          ∀ Zin : Finset V, ∀ w : V → ℝ, (∀ z ∈ Zin, 0 ≤ w z) →
            ∃ (T : SpanningTree G) (Z : Finset V),
              IsWeightedRamseySpanningTree true G T Zin w Z (C * t)
                  (max 0 (1 - c * (Real.logb 2 t +
                    Real.logb 2 (Real.logb 2 (4 * aspectRatio (rdist G) Zin))) / t)) ∧
                DiamStretchLe G T CD := by sorry

end RamseyLST.Main
