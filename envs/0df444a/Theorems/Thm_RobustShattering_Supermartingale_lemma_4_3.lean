-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_lemma_4_3
-- name    : RobustShattering.Supermartingale.lemma_4_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:30.999207+00:00
-- url     : https://prove2.me/theorems/b4403768-2597-490a-90c2-243397754448
-- title:
--   Lemma 4.3 (Shattering Lemma) — separated-set bound ⇒ no large c₂-independent x-connected set inside B
-- statement:
--   Let $G=(V,E)$ be a graph on $n$ vertices in which every vertex has degree at most $\Delta$, where $\Delta\ge2$; let $c_2,x\ge0$ be integers and $c_3\ge0$ a real number. Let $B\subseteq V$ be a random vertex set, defined on an arbitrary probability space.
--   1. If
--   $$\Pr[S\subseteq B]\le\Delta^{-(x+c_3+2)|S|}\tag{4}$$
--   for every $c_2$-independent set $S$ of size $\lceil\log_\Delta n\rceil$, then with probability at least $1-n^{-c_3}$ every $c_2$-independent $x$-connected set (distances measured in $G$) contained in $B$ has size at most $\lceil\log_\Delta n\rceil$.
--   2. More generally, for every integer $t\ge\log_\Delta n$: if (4) holds for every $c_2$-independent set of size $t$, then with probability at least $1-\Delta^{-c_3t}$ every $c_2$-independent $x$-connected set contained in $B$ has size at most $t$.
--
--   This is the classical shattering lemma in its separated-set form: it needs no independence between the events $[v\in B]$, only the bound (4) on separated sets. Corollary 4.4 derives small connected components from it, and Theorem 4.11 Part 2 is its instance for shatterable processes.
--
--   **Formalization Note.** The random set is a function $B:\Omega\to\mathrm{Set}\,V$ on a probability space $(\Omega,P)$, with no measurability assumption; every probability is the (outer) measure of the corresponding set. "With probability at least $1-\delta$, every such set has size at most $m$" is stated as $P(\text{some such set has more than } m \text{ vertices})\le\delta$. $\log_\Delta n$ is `Real.logb Δ n`, $\lceil\cdot\rceil$ is `Nat.ceil`, and powers with real exponents are `Real.rpow`, wrapped in `ENNReal.ofReal`.
--
--   Differences from the source:
--   - generalization: graph with maximum degree $\Delta$ → every vertex degree at most $\Delta$; reason: a graph of maximum degree $\Delta$ satisfies the hypothesis, and the proof uses only the upper bound (the counting of Lemma 4.2 for $\Delta\ge3$; for $\Delta=2$ the graph is a disjoint union of paths and cycles)
--   - encoding: "a process that generates a random subset $B$" → an arbitrary probability space $(\Omega,P)$ and an arbitrary map $B:\Omega\to\mathrm{Set}\,V$, probabilities as outer measures in hypothesis and conclusion; reason: equal to the probabilities when the events are measurable; the paper places no condition on the process
--   - encoding: "with probability at least $1-\delta$ every such set has size at most $m$" → the measure of "some such set has more than $m$ vertices" is at most $\delta$; reason: complement of the success event; stated as an upper bound so that no measurability is needed
--   - encoding: $\log_\Delta n$, $\lceil\cdot\rceil$, $\Delta^{-(x+c_3+2)|S|}$, $n^{-c_3}$, $\Delta^{-c_3t}$ → `Real.logb`, `Nat.ceil`, `Real.rpow` inside `ENNReal.ofReal`; reason: Lean conventions, with $\Delta\ge2$ and $n\ge0$ every value is the paper's
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 12, Lemma 4.3

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected

open MeasureTheory

namespace RobustShattering.Supermartingale

/-- Lemma 4.3 (Shattering Lemma, p. 12): let `G` be a graph on `n` vertices with every degree at
most `Δ ≥ 2`, let `c₂, x ≥ 0` be integers and `c₃ ≥ 0`, and let `B` be a random vertex set on an
arbitrary probability space `(Ω, P)`.
1. If `P[S ⊆ B] ≤ Δ^{-(x + c₃ + 2)|S|}` for every `c₂`-independent `S` of size `⌈log_Δ n⌉`, then
   the probability that some `c₂`-independent `x`-connected set `S ⊆ B` has more than
   `⌈log_Δ n⌉` vertices is at most `n^{-c₃}`.
2. For every integer `t ≥ log_Δ n`: if the same bound holds for every `c₂`-independent `S` of
   size `t`, then the probability that some `c₂`-independent `x`-connected set `S ⊆ B` has more
   than `t` vertices is at most `Δ^{-c₃ t}`.
Probabilities of events about `B` are outer measures; `B` need not be measurable. -/
theorem lemma_4_3 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c₂ x : ℕ) (c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Set V) :
    ((∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) →
        S.card = ⌈Real.logb Δ (Fintype.card V)⌉₊ →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) →
      P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
          XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧
          ⌈Real.logb Δ (Fintype.card V)⌉₊ < S.card} ≤
        ENNReal.ofReal ((Fintype.card V : ℝ) ^ (-c₃))) ∧
    (∀ t : ℕ, Real.logb Δ (Fintype.card V) ≤ (t : ℝ) →
      (∀ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) → S.card = t →
          P {ω | (S : Set V) ⊆ B ω} ≤
            ENNReal.ofReal ((Δ : ℝ) ^ (-(((x : ℝ) + c₃ + 2) * (S.card : ℝ))))) →
        P {ω | ∃ S : Finset V, LocalLLL.Main.separated G c₂ (S : Set V) ∧
            XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ t < S.card} ≤
          ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * (t : ℝ))))) := by sorry

end RobustShattering.Supermartingale
