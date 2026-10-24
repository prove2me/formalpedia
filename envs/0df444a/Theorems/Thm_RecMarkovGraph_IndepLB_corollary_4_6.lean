-- Prove2me | Theorems.Thm_RecMarkovGraph_IndepLB_corollary_4_6
-- name    : RecMarkovGraph.IndepLB.corollary_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:53.005472+00:00
-- url     : https://prove2.me/theorems/16ed28f5-a762-4fdb-8b8c-231b65e6c6e4
-- title:
--   Corollary 4.6, p. 11 — for a decay chain with β ∈ (0,1), E S_n/log n → 1/β and S_n/log n →p 1/β
-- statement:
--   Let $Y_1,Y_2,\dots$ be a Markov chain of Bernoulli random variables, i.e.
--   $$\mathbb P\{Y_{n+1}=y_{n+1}\mid Y_1=y_1,\dots,Y_n=y_n\}=\mathbb P\{Y_{n+1}=y_{n+1}\mid Y_n=y_n\}\quad(n\ge1),$$
--   and suppose that for some $\beta\in(0,1)$
--   $$\mathbb P\{Y_{n+1}=1\mid Y_n=0\}=\mathbb P\{Y_n=1\},\qquad \mathbb P\{Y_{n+1}=1\mid Y_n=1\}=(1-\beta)\,\mathbb P\{Y_n=1\},$$
--   and that $\mathbb P\{Y_1=1\}>0$. Let $S_n=Y_1+\dots+Y_n$ and $\mathcal Y_n=S_n/\log n$. Then
--   $$\mathbb E\mathcal Y_n\longrightarrow\frac1\beta\qquad\text{and}\qquad \mathcal Y_n\xrightarrow{\ p\ }\frac1\beta .$$
--
--   With $\beta=\gamma$ this is the law of large numbers for the row sums of $G^r_{n,p}$ (Lemma 3.2), and it is the result the proof of Theorem 2.2 invokes.
--
--   Differences from the source:
--   - encoding: β ∈ [0, 1) → 0 < β < 1; reason: at β = 0 the limit 1/β is undefined (Lean's 1/0 = 0 would assert a false limit 0)
--   - reading: no condition on P{Y_1 = 1} → 0 < P{Y 0 = 1}; reason: the corollary is "a special case of Theorem 4.4", i.e. of recursion (3), which assumes x_1 ∈ (0, 1) (p. 9); the chain Y ≡ 0 meets the printed hypotheses and has E𝒴_n = 0
--   - generalization: P{Y_1 = 1} = x_1 < 1 (recursion (3)) → P{Y 0 = 1} ∈ (0, 1]; reason: at P{Y_1 = 1} = 1 the chain is a chain of the same kind shifted by one step, with P{Y_2 = 1} = 1 − β ∈ (0, 1), so the corollary still holds; the goal at p = 1 needs this case; specializes to x_1 ∈ (0, 1)
--   - encoding: Markov property and conditional probabilities; E𝒴_n; Y_1, Y_2, … → IsDecayChain P Y β (multiplicative conditionals, Markov property for every y : ℕ → ℝ); (∫ S_n ∂P)/log n; Y 0, Y 1, …; reason: multiplicative form avoids conditioning on null events; E𝒴_n = E S_n/log n; 0-based index
--   - encoding: ξ_n concentrates to c: P{|ξ_n − c| ⩽ ε} → 1 for every ε > 0 (p. 4) → ∀ ε > 0, Tendsto (fun n => P{|ξ_n − c| ≤ ε}) atTop (𝓝 1); reason: the paper's own definition, with ≤ ε
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 11, Corollary 4.6; 𝒴_n := S_n/log n, p. 10

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory Finset Filter Topology

theorem corollary_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hY : IsDecayChain P Y β)
    (hY0 : 0 < P.real {ω | Y 0 ω = 1}) :
    Tendsto (fun n : ℕ => (∫ ω, ∑ k ∈ range n, Y k ω ∂P) / Real.log n) atTop (𝓝 (1 / β)) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
          P.real {ω | |(∑ k ∈ range n, Y k ω) / Real.log n - 1 / β| ≤ ε}) atTop (𝓝 1) := by sorry

end RecMarkovGraph.IndepLB
