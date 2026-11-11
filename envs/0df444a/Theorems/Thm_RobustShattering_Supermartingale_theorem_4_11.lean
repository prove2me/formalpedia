-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_theorem_4_11
-- name    : RobustShattering.Supermartingale.theorem_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:57.173435+00:00
-- url     : https://prove2.me/theorems/d22cff4d-9859-4bf4-8e30-f8566a6524e6
-- title:
--   Theorem 4.11 — shattering from local supermartingales: Pr[S ⊆ B] ≤ (X/Y)^|S|, no large separated x-connected sets, components of size ≤ (Δ^{2c}+1)⌈log_Δ n⌉ w.h.p.
-- statement:
--   Let $G=(V,E)$ be a graph on $n$ vertices in which every vertex has degree at most $\Delta$, where $\Delta\ge2$; let $c,x\in\mathbb N$, $c_3\ge0$, $X\in\mathbb R_{\ge0}$ and $Y\in\mathbb R_{>0}$. Consider a $(c,X,Y)$-shatterable $T$-step process (Definition 4.7: independent randomness $R_i(v)$ for $v\in V$, $i\in[T]$; post-shattering set $B$, an arbitrary function of all the randomness; cost functions with low initial cost $\le X$, the local supermartingale property and post-shattering cost $\ge Y$). Then:
--   1. for every $2c$-independent set $S\subseteq V$,
--   $$\Pr[S\subseteq B]\le\Big(\frac XY\Big)^{|S|};$$
--   2. if $Y/X\ge\Delta^{x+c_3+2}$, then for every $t\ge\log_\Delta n$, with probability at least $1-\Delta^{-c_3t}$, every $2c$-independent $x$-connected set (distances measured in $G$) contained in $B$ has size at most $t$;
--   3. if $Y/X\ge\Delta^{2c+4}$, then with probability at least $1-1/n$ every connected component of $G[B]$ has at most $(\Delta^{2c}+1)\lceil\log_\Delta n\rceil$ vertices.
--
--   The theorem is the paper's repaired shattering framework: it replaces the bounded-radius independence that earlier shattering arguments assumed, and which fails for long pre-shattering phases, by a local supermartingale certificate, and still delivers the separated-set bound and small post-shattering components. "With high probability in $n$" is the paper's own convention, probability at least $1-1/n$ (p. 20).
--
--   **Formalization Note.** Probabilities are (outer) measures under the joint product law `processMeasure μ` of all the randomness; $B$ need not be measurable, and the bounds then hold for the outer measure, which is at least as strong. "With probability at least $1-\delta$, property $Q$ holds" is stated as "the measure of the failure of $Q$ is at most $\delta$". The ratio conditions $Y/X\ge\Delta^k$ are stated as $X\cdot\Delta^k\le Y$, so that $X=0$ (ratio $+\infty$) needs no division. Part 2 is stated for every real $t\ge\log_\Delta n$, failure meaning some such set has more than $t$ vertices. A component with more than $m$ vertices exists exactly when some $C\subseteq B$ with $G[C]$ connected has more than $m$ vertices. $\log_\Delta n$ is `Real.logb Δ n`, $\lceil\cdot\rceil$ is `Nat.ceil`, and $1/n$ is `ENNReal.ofReal (1 / n)`.
--
--   Differences from the source:
--   - generalization: graph with maximum degree $\Delta$ → every vertex degree at most $\Delta$; reason: a graph of maximum degree $\Delta$ satisfies the hypothesis, and the proof (Lemma 4.10, Lemma 4.3, Corollary 4.4) uses only the upper bound
--   - generalization: Part 2's "for any $t\ge\log_\Delta n$" → every real $t\ge\log_\Delta n$; reason: covers the integer $t$ of Lemma 4.3, which the proof invokes, as a special case, and is the literal reading of the theorem's sentence
--   - reading: "let $c,c_3,x\ge0$" → $c,x\in\mathbb N$ and $c_3\in\mathbb R$ with $c_3\ge0$; reason: $c\in\mathbb N$ in Definition 4.7, and $x$-connectedness is defined for integers $x$ (§2.7)
--   - encoding: $Y/X\ge\Delta^{x+c_3+2}$ and $Y/X\ge\Delta^{2c+4}$ → $X\cdot\Delta^{x+c_3+2}\le Y$ and $X\cdot\Delta^{2c+4}\le Y$; reason: equivalent for $X>0$; for $X=0$ the ratio is $+\infty$ and both forms hold
--   - encoding: "with high probability in $n$" → failure probability at most $1/n$; reason: the paper's own definition (p. 20)
--   - encoding: probabilities → (outer) measures under the product law, with no measurability of $B$; "with probability at least $1-\delta$, $Q$" → measure of the failure of $Q$ at most $\delta$; reason: equal to the probabilities when the events are measurable; the outer-measure bound is at least as strong
--   - encoding: "every connected component of $G[B]$ has size at most $m$" → no $C\subseteq B$ with $G[C]$ connected has more than $m$ vertices; reason: components are connected, and every connected subset of $B$ lies in one component
--   - encoding: steps $1,\dots,T$, $\log_\Delta n$, $\lceil\cdot\rceil$, real powers → `Fin T` (Lean step $k$ = the paper's step $k+1$), `Real.logb`, `Nat.ceil`, `Real.rpow` inside `ENNReal.ofReal`; reason: Lean conventions, the same values for $\Delta\ge2$
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 16, Theorem 4.11; w.h.p. convention p. 20, §5.1

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_XConnected
import Definitions.Def_RobustShattering_Supermartingale_Shatterable

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Supermartingale

/-- Theorem 4.11 (Shattering from local supermartingales, p. 16): let `G` be a graph on `n`
vertices with every degree at most `Δ ≥ 2`, let `c, x ∈ ℕ`, `c₃ ≥ 0`, `X ≥ 0`, `Y > 0`, and let
the `T`-step process with independent randomness `(Ω u k, μ u k)` and post-shattering set `B` be
`(c, X, Y)`-shatterable. Then
1. `P[S ⊆ B] ≤ (X / Y)^{|S|}` for every `2c`-independent `S`;
2. if `X · Δ^{x + c₃ + 2} ≤ Y`, then for every real `t ≥ log_Δ n` the probability that some
   `2c`-independent `x`-connected set `S ⊆ B` has more than `t` vertices is at most `Δ^{-c₃ t}`;
3. if `X · Δ^{2c + 4} ≤ Y`, then the probability that some connected component of `G[B]` has
   more than `(Δ^{2c} + 1) ⌈log_Δ n⌉` vertices is at most `1 / n`.
Probabilities of events about `B` are outer measures under the product law; `B` need not be
measurable. -/
theorem theorem_4_11 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (c x : ℕ) (c₃ : ℝ) (hc₃ : 0 ≤ c₃)
    (X Y : ℝ≥0) (hY : 0 < Y) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (B : Randomness Ω → Set V) (hP : Shatterable G c X Y μ B) :
    (∀ S : Finset V, LocalLLL.Main.separated G (2 * c) (S : Set V) →
      processMeasure μ {ω | (S : Set V) ⊆ B ω} ≤ (((X / Y) ^ S.card : ℝ≥0) : ℝ≥0∞)) ∧
    ((X : ℝ) * (Δ : ℝ) ^ ((x : ℝ) + c₃ + 2) ≤ (Y : ℝ) →
      ∀ t : ℝ, Real.logb Δ (Fintype.card V) ≤ t →
        processMeasure μ {ω | ∃ S : Finset V, LocalLLL.Main.separated G (2 * c) (S : Set V) ∧
            XConnected G x (S : Set V) ∧ (S : Set V) ⊆ B ω ∧ t < (S.card : ℝ)} ≤
          ENNReal.ofReal ((Δ : ℝ) ^ (-(c₃ * t)))) ∧
    ((X : ℝ) * (Δ : ℝ) ^ (2 * c + 4) ≤ (Y : ℝ) →
      processMeasure μ {ω | ∃ C : Finset V, (C : Set V) ⊆ B ω ∧
          (G.induce (C : Set V)).Connected ∧
          (Δ ^ (2 * c) + 1) * ⌈Real.logb Δ (Fintype.card V)⌉₊ < C.card} ≤
        ENNReal.ofReal (1 / (Fintype.card V : ℝ))) := by sorry

end RobustShattering.Supermartingale
