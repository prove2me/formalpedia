-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_reduction_graph_properties
-- name    : SparsestCutOracle.Main.reduction_graph_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:44:19.731261+00:00
-- url     : https://prove2.me/theorems/a9327263-fe6a-4a16-a94b-d39fd42c6171
-- title:
--   Claim 3 — Properties of the constructed reduction graph
-- statement:
--   Here $n=|V|$, $m$ is the number of listed edges, $\Pi=\sum_i\pi(i)$, and $z=|V_H|$. The quantities $k_i,\mu,M$, the copy set, and the parent map are the constructed objects of the preceding definition.
--
--   Fix $\xi,R>0$ and choose $c_M$ sufficiently large before the instance. Construct $H$, its copy set $A_H$, vectors, $\mu$ and $M$ exactly as in §5.2 from a connected graph and nonnegative weights of total mass $\Pi>0$. Assume $\pi(A)\ge\Pi/2$, $\|w_i\|\le R$ on $A$, and weighted spread at least $\xi\Pi^2$. Then
--
--   $$n\le z\le(1+64R^2/\xi)n,\quad
--   m\le|E_H|\le(1+128R^2/\xi)m,\quad
--   \frac{\Pi}{4\mu}\le z\le\frac{2\Pi}{\mu}.$$
--
--   Moreover $|A_H|\ge z/2$, every copy vector has squared norm at most two, and its ordered-pair spread is at least $(7\xi/(32R^2))z^2$. Lifting a vertex set to all its copies preserves cut capacity, every lifted cut has capacity below $M$, and every cut of $H$ below $M$ has a unique preimage. These are all four numbered conclusions of Claim 3.
--
--   Differences from the source:
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: Θ(n), Θ(m), and some ξ′>0 depending only on ξ,R → explicit upper constants 1+64R²/ξ and 1+128R²/ξ, lower constants one, and ξ′=7ξ/(32R²); reason: Equation (12) bounds N; connectedness gives n≤2m; the spread calculation on p.33 yields the stated ξ′
--   - encoding: replacement vertices and arbitrary representatives → a finite dependent sum of copy indices, relabeled by Fin z, with the zeroth copy as representative; reason: this relabels exactly the graph of §5.2; the cut bijection is stated in both directions with uniqueness
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 32, Claim 3; construction pp. 31–32; proof p. 33

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Reduction

namespace SparsestCutOracle.Main

/-- Claim 3, p.32. The proof yields explicit size constants and ξ'=7ξ/(32R²). -/
theorem reduction_graph_properties (ξ R : ℝ) (hξ : 0 < ξ) (hR : 0 < R) :
    ∃ cM₀ : ℝ, 1 ≤ cM₀ ∧ ∀ cM : ℝ, cM₀ ≤ cM →
      ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (X : Mat n)
        (A : Finset (Fin n)) (α : ℝ),
        2 ≤ n → G.NoLoops → G.Connected → (∀ v, 0 ≤ π v) → 0 < totalWeight π →
        X.PosSemidef → totalWeight π / 2 ≤ mass π A → 0 < α →
        (∀ i ∈ A, X i i ≤ R ^ 2) → ξ * totalWeight π ^ 2 ≤ spread π X A →
        let z := redZ π A R ξ
        let μ := reductionMu π A R ξ
        let M := reductionM G π A R ξ α cM
        let H := reductionGraph G π A R ξ α cM
        let AH := redA π A R ξ
        let XH := redGram π A R ξ X
        (n ≤ z ∧ (z : ℝ) ≤ (1 + 64 * R ^ 2 / ξ) * n ∧
          G.length ≤ H.length ∧
          (H.length : ℝ) ≤ (1 + 128 * R ^ 2 / ξ) * G.length) ∧
        ((1 / 4 : ℝ) * totalWeight π / μ ≤ z ∧ (z : ℝ) ≤ 2 * totalWeight π / μ) ∧
        (XH.PosSemidef ∧ (z : ℝ) / 2 ≤ AH.card ∧
          (∀ h ∈ AH, XH h h ≤ 2) ∧
          (7 * ξ / (32 * R ^ 2)) * (z : ℝ) ^ 2 ≤ spread (fun _ => 1) XH AH) ∧
        ((∀ S : Finset (Fin n),
            cut H.toWGraph (liftCut π A R ξ S) (liftCut π A R ξ S)ᶜ = cut G.toWGraph S Sᶜ ∧
            cut H.toWGraph (liftCut π A R ξ S) (liftCut π A R ξ S)ᶜ < M) ∧
          ∀ T : Finset (Fin z), cut H.toWGraph T Tᶜ < M →
            ∃! S : Finset (Fin n), liftCut π A R ξ S = T) := by sorry

end SparsestCutOracle.Main
