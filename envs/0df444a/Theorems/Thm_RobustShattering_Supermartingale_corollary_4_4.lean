-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_corollary_4_4
-- name    : RobustShattering.Supermartingale.corollary_4_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T20:42:43.390244+00:00
-- url     : https://prove2.me/theorems/8552312b-ec98-4d86-bc91-b967786fcade
-- title:
--   Corollary 4.4 — separated-set bound with exponent c₂+c₃+3 ⇒ components of G[B] have size ≤ t(Δ^{c₂}+1)
-- statement:
--   Let $G=(V,E)$ be a graph on $n$ vertices in which every vertex has degree at most $\Delta$, where $\Delta\ge2$; let $c_2\ge0$ be an integer, $c_3\ge0$ a real number, and $t\ge\log_\Delta n$ an integer. Let $B\subseteq V$ be a random vertex set, defined on an arbitrary probability space, such that
--   $$\Pr[S\subseteq B]\le\Delta^{-(c_2+c_3+3)|S|}\tag{5}$$
--   for every $c_2$-independent set $S$ of size $t$. Then with probability at least $1-\Delta^{-c_3t}$ every connected component of the induced subgraph $G[B]$ has at most $t(\Delta^{c_2}+1)$ vertices.
--
--   This converts the separated-set bound into the usual conclusion of shattering, small residual components, which is what the post-shattering phase of a distributed algorithm needs. Theorem 4.11 Part 3 is its instance with $c_2=2c$, $c_3=1$, $t=\lceil\log_\Delta n\rceil$.
--
--   **Formalization Note.** "Some connected component of $G[B]$ has more than $m$ vertices" is stated as "some finite $C\subseteq B$ with $G[C]$ connected has more than $m$ vertices"; the two are equivalent, since components are connected and every connected subset of $B$ lies in one component. The random set is a function $B:\Omega\to\mathrm{Set}\,V$ on a probability space $(\Omega,P)$ with no measurability assumption, and probabilities are outer measures. $\log_\Delta n$ is `Real.logb Δ n`, real powers are `Real.rpow` inside `ENNReal.ofReal`.
--
--   Differences from the source:
--   - generalization: graph with maximum degree $\Delta$ → every vertex degree at most $\Delta$; reason: a graph of maximum degree $\Delta$ satisfies the hypothesis, and the proof uses only the upper bound ($|B^{c_2}(v)|\le\Delta^{c_2}+1$ and Lemma 4.3)
--   - encoding: "a process that generates a random subset $B$" → an arbitrary probability space $(\Omega,P)$ and an arbitrary map $B:\Omega\to\mathrm{Set}\,V$, probabilities as outer measures in hypothesis and conclusion; reason: equal to the probabilities when the events are measurable; the paper places no condition on the process
--   - encoding: "with probability at least $1-\Delta^{-c_3t}$ every connected component of $G[B]$ has size at most $t(\Delta^{c_2}+1)$" → the measure of "some $C\subseteq B$ with $G[C]$ connected has more than $t(\Delta^{c_2}+1)$ vertices" is at most $\Delta^{-c_3t}$; reason: complement of the success event, and a component larger than $m$ exists exactly when a connected subset of $B$ larger than $m$ exists
--   - encoding: $\log_\Delta n$, $\Delta^{-(c_2+c_3+3)|S|}$, $\Delta^{-c_3t}$ → `Real.logb`, `Real.rpow` inside `ENNReal.ofReal`; reason: Lean conventions, the same values for $\Delta\ge2$
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 13, Corollary 4.4

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel

open MeasureTheory

namespace RobustShattering.Supermartingale

/-- Corollary 4.4 (p. 13): let `G` be a graph on `n` vertices with every degree at most `Δ ≥ 2`,
let `c₂ ≥ 0` be an integer, `c₃ ≥ 0`, and `t ≥ log_Δ n` an integer. If a random vertex set `B` on
an arbitrary probability space satisfies `P[S ⊆ B] ≤ Δ^{-(c₂ + c₃ + 3)|S|}` for every
`c₂`-independent `S` of size `t`, then the probability that some connected component of `G[B]`
has more than `t (Δ^{c₂} + 1)` vertices is at most `Δ^{-c₃ t}`. A component of `G[B]` with more
than `m` vertices exists exactly when some `C ⊆ B` with `G[C]` connected has more than `m`
vertices. Probabilities are outer measures; `B` need not be measurable. -/
theorem corollary_4_4 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c₂ : ℕ) (c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    (t : ℕ) (ht : Real.logb Δ (Fintype.card V) ≤ (t : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Set V)
    (hB : ∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = t →
      P {ω | (S : Set V) ⊆ B ω} ≤
        ENNReal.ofReal ((Δ : ℝ) ^ (-(((c₂ : ℝ) + c₃ + 3) * (S.card : ℝ))))) :
    P {ω | ∃ C : Finset V, (C : Set V) ⊆ B ω ∧ (G.induce (C : Set V)).Connected ∧
        t * (Δ ^ c₂ + 1) < C.card} ≤
      ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (t : ℝ)))) := by sorry

end RobustShattering.Supermartingale
