-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_corollary_4_7
-- name    : PDynTreeEmbed.Main.corollary_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:13.048836+00:00
-- url     : https://prove2.me/theorems/701178ad-f8f1-4997-9933-3281f45f5bce
-- title:
--   Corollary 4.7 — Algorithm 2 outputs an LDD with slack O(log n)
-- statement:
--   There is a universal constant $C$ such that for every $c>0$ there is $\kappa$ with the following property. For every connected graph on $n\ge2$ vertices with positive integer weights, every $D>0$ and every valid execution of Algorithm 2 with parameter $D$:
--   $$\Pr\big[\text{every cluster has weak diameter}\le\kappa D\log_2 n\big]\ge1-n^{-c},\qquad \Pr[u,v\ \text{in distinct clusters}]\le C\,\frac{\mathrm{dist}_G(u,v)}{D}\ \ \forall u,v.$$
--   With diameter parameter $D'=\kappa D\log_2 n$ this is an LDD with slack $C\kappa\log_2 n=O(\log n)$.
--
--   Differences from the source:
--
--   - reading: Algorithm 2 outputs an LDD with slack O(log n) → ∃ C ∀ c > 0 ∃ κ: P[some cluster has weak diameter > κ·D·log₂ n] ≤ n^{−c} and P[u, v separated] ≤ C·dist_G(u, v)/D for all u, v; reason: the proof's statement before 'rescaling D by a Θ(log n) factor'; with D' = κ D log₂ n it is the LDD definition of p. 2
--   - reading: the output of Algorithm 2 ('compute X_i such that …', Blur's 'compute X_k such that …') → every valid execution: selectors X (function of π, R⃗) and Y (blur stage k of center w a function of π, R⃗ and r_{w,1..k}) satisfying (5), Algorithm 2 line 4 and Algorithm 3 line 5 (IsAlg2Exec); reason: a nondeterministic choice; quantifying over all choices is its meaning, and Lemmas 6.3/7.10 verify exactly these properties for the dynamic algorithms
--   - encoding: π uniform, R_w ∼ Exp(1/D) i.i.d. (rate 1/D, mean D) per vertex, blur radii r_{w,k} ∼ Unif[0, α^{k−1}σ], all independent → any probability space with a random outcome ζ satisfying IsAlg2Law (laws via Measure.map, iIndepFun, IndepFun); reason: a statement about every realization of the law is the statement about the law
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
--   - encoding: the input graph (standing assumptions) → connected, positive integer weights (HasPosWeights); reason: the standing assumptions of p. 13
--   - generalization: polynomially bounded weights W ≤ n^{O(1)} (standing assumption) → any W (the statement has no constant depending on W); reason: the bound W ≤ n^{c_W} is a special case
--   - encoding: cluster, weak diameter → x, y in the same cluster iff Center x = Center y; weak diameter compared through rdist; reason: clusters are the classes of Center
--   - encoding: the probability of an event of Algorithm 2's output → the blur selectors are measurable (IsMeasurableExec), as in Lemmas 4.5, 4.6 and Theorem 4.8; reason: a randomized algorithm's output is a random variable; without measurability the bound would be on an outer measure
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 18, Corollary 4.7

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Static
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Corollary 4.7** (p. 18): Algorithm 2 outputs an LDD with slack `O(log n)`. There is a universal
`C` such that for every `c > 0` there is `κ` with the following property. For every connected graph on
`n ≥ 2` vertices with positive integer weights, every `D > 0` and every valid execution of
Algorithm 2 with parameter `D` whose blur selectors are measurable: with probability at least `1 − n^{−c}` every cluster has weak
diameter at most `κ·D·log₂ n`, and every pair `u, v` lies in distinct clusters with probability at
most `C·dist_G(u, v)/D`. (With diameter parameter `D' = κ·D·log₂ n` the slack is `Cκ·log₂ n`.) -/
theorem corollary_4_7 : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∃ κ : ℝ, 0 < κ ∧
    ∀ (n : ℕ) (G : WGraph (Fin n)), 2 ≤ n → G.adj.Connected → G.HasPosWeights →
      ∀ (D : ℝ), 0 < D →
      ∀ (X : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → Finset (Fin n))
        (Y : Equiv.Perm (Fin n) → (Fin n → ℝ) → Fin n → (ℕ → ℝ) → ℕ → Finset (Fin n)),
        IsAlg2Exec G D X Y →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ζ : Ω → Outcome n),
          IsAlg2Law P n D ζ → IsMeasurableExec Y →
          P {ω | ∃ x y : Fin n, center Y D (ζ ω) x = center Y D (ζ ω) y ∧
              κ * D * log2 n < G.rdist x y} ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) ∧
            ∀ u v : Fin n, P {ω | center Y D (ζ ω) u ≠ center Y D (ζ ω) v} ≤
              ENNReal.ofReal (C * G.rdist u v / D) := by sorry

end PDynTreeEmbed.Main
