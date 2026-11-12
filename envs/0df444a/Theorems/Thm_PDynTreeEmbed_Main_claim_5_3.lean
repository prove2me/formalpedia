-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_claim_5_3
-- name    : PDynTreeEmbed.Main.claim_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:55.037691+00:00
-- url     : https://prove2.me/theorems/d310383b-737d-4739-b0d6-2af3811dcdf1
-- title:
--   Claim 5.3 — the expected number of candidates ever within D of winning is at most e(1 + H_|S|)
-- statement:
--   Let $G^{(0)},\dots,G^{(T)}$ be the graphs of a partially dynamic instance fixed in advance, $v$ a vertex, $D>0$, $S\subseteq V$ nonempty, and $R_x\sim\mathrm{Exp}(1/D)$ independent. For $x\in S$ let $\alpha^{(t)}_x=\mathrm{dist}_{G^{(t)}}(x,v)$, $\rho^{(t)}_x=\alpha^{(t)}_x-R_x$, $\mu^{(t)}_{-u}(S)=\min\{0,\min_{x\in S\setminus\{u\}}\rho^{(t)}_x\}$ and $W^{(t)}_v(S)=\{u\in S:\rho^{(t)}_u\le\mu^{(t)}_{-u}(S)+D\}$. Then
--   $$\mathbb E\Big[\Big|\bigcup_t W^{(t)}_v(S)\Big|\Big]\le e\cdot(1+H_{|S|}).$$
--   It is the step from Lemma 2.1 to the improving-set bound (14).
--
--   Differences from the source:
--
--   - generalization: graphs undergoing edge insertions (the setting of Lemma 5.2, in which the claim is printed) → any partially dynamic instance, insertions or deletions; reason: the union over t does not depend on the order of the graphs (p. 22), and the insertion case is the special case κ = incr
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: radii R_x for x ∈ S → a radius for every vertex, i.i.d. Exp(1/D) on any probability space; only those of S are used; expectation as a lintegral; reason: the same law on the coordinates in S
--   - encoding: the graph sequence (standing assumptions: integral weights in [1, W], connected throughout) → IsInstance W G₀ κ σ, G^(t) = graphAt G₀ σ t, t = 0..T; reason: the standing assumptions of p. 13
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 21, Claim 5.3

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Improving
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Claim 5.3** (p. 21). Let `G^(0), …, G^(T)` be the graphs of a partially dynamic instance
(fixed in advance), `v` a vertex, `S` a nonempty vertex set, `D > 0`, and let the radii `R_x`
(`x ∈ V`) be independent `Exp(1/D)`. With `ρ^(t)_x = dist_{G^(t)}(x, v) − R_x`,
`µ^(t)_{−u}(S) = min{0, min_{x ∈ S∖{u}} ρ^(t)_x}` and
`W^(t)_v(S) = {u ∈ S : ρ^(t)_u ≤ µ^(t)_{−u}(S) + D}`, the expected size of `⋃_t W^(t)_v(S)` is at
most `e·(1 + H_{|S|})`. -/
theorem claim_5_3 (n W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n))
    (hinst : IsInstance W G₀ κ σ) (v : Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (D : ℝ) (hD : 0 < D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : Fin n → Ω → ℝ) (hind : iIndepFun R P)
    (hlaw : ∀ x, P.map (R x) = expMeasure (1 / D)) :
    ∫⁻ ω, (((Finset.range (σ.length + 1)).biUnion fun t =>
        nearWinners (graphAt G₀ σ t) D (fun x => R x ω) S v).card : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (Real.exp 1 * (1 + (harmonic S.card : ℝ))) := by sorry

end PDynTreeEmbed.Main
