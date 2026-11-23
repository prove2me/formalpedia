-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_Supplement_theorem_14
-- name    : UnsplitCVRP.Combinatorial.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:42:32.545802+00:00
-- url     : https://prove2.me/theorems/596dd4cd-638c-465d-b3ff-d3a74f13c672
-- title:
--   Theorem 14, p. 11 (corrected: inner min is max) — the better of Algorithm 2 and the Blauth–Traub–Vygen algorithm
-- statement:
--   Use the setting of Theorem 2: an instance of the CVRP with unsplittable demands, $0<\delta<1$, an optimal Configuration-LP solution $x^*$, a TSP tour $\mathrm{tour}(U)$ of cost at most $\alpha$ times the TSP optimum on each client set $U$, and the radial sum $\mathcal D=\sum_{v\in V}2d_v\,c(r,v)$.
--
--   Theorem 13 (Blauth, Traub and Vygen) is quoted, not proved, in the paper, so it enters as a hypothesis: $f$ is a function and, for every $\delta'\in(0,1)$, $B(\delta')$ is a feasible solution such that $c(B(\delta'))\le(3+f(\delta'))\cdot c(R)$ for every feasible solution $R$ with $(1-\delta')\,c(R)\le\mathcal D$. Then for every $\delta'\in(0,1)$, the solution obtained by taking, for each outcome of Algorithm 2, the cheaper of Algorithm 2's output and $B(\delta')$ satisfies
--
--   1. for every outcome there is a feasible solution of cost at most that of the cheaper one, and
--   2. for every feasible solution $R$,
--   $$\mathbb E\Big[\min\big\{c(\mathcal T\cup\mathcal T'),\,c(B(\delta'))\big\}\Big]\ \le\ \max\Big\{3+f(\delta'),\ \ln2+\alpha+\frac{1-\delta'}{1-\delta}\Big\}\cdot c(R).$$
--
--   Since $\delta'$ is arbitrary, the guarantee is the minimum of the right-hand side over $0<\delta'<1$. Corollary 15 uses it to beat $\ln2+\alpha+1$ by a constant when $\alpha>2-\ln2$.
--
--   **Formalization Note** Theorem 13 asserts $c(B(\delta'))\le(3+f(\delta'))\,\mathrm{opt}$ whenever $\mathcal D\ge(1-\delta')\,\mathrm{opt}$, with $f>0$; since $\mathrm{opt}\le c(R)$, this implies the per-solution hypothesis used here, so the theorem applies to the algorithm of Theorem 13. Expectations and costs are as in Theorem 2; the running time is not formalized.
--
--   Differences from the source:
--   - correction: guarantee min over δ′ of min{3 + f(δ′), ln 2 + α + (1−δ′)/(1−δ)} → for each δ′ the guarantee max{3 + f(δ′), ln 2 + α + (1−δ′)/(1−δ)}; reason: the proof on p. 11 gives one bound in the case 𝒟 ≤ (1−δ′)·opt and the other in the case 𝒟 > (1−δ′)·opt, which yields only the larger of the two, and Corollary 15's proof requires both terms to lie below ln 2 + α + 1; with the printed inner min the guarantee would tend to ln 2 + α as δ′ → 1, which nothing in the paper supports
--   - reading: the outer min over 0 < δ′ < 1 → the bound for every δ′ ∈ (0, 1); reason: an approximation for each δ′ is what the proof gives ("This holds for any 0 < δ′ < 1"), and the minimum is taken by choosing δ′
--   - reading: "for any constant δ > 0" → 0 < δ < 1; reason: as in Theorem 2, the ratio (1−δ′)/(1−δ) has content only for δ < 1; wider than §4's standing range (0, 1/2] (p. 9), and the bound of Theorem 2's analysis holds on all of (0, 1)
--   - encoding: the algorithm of Theorem 13 [BTV21] → a given f and solutions B(δ′) satisfying the per-solution form of Theorem 13's guarantee; reason: Theorem 13 is quoted from [BTV21], not proved here, and its guarantee implies this form because opt ≤ c(R) and 3 + f > 0
--   - generalization: f : ℝ>0 → ℝ>0 with f(δ′) → 0, guarantee for all δ′ > 0 → any f : ℝ → ℝ, guarantee assumed only for δ′ ∈ (0, 1); reason: the proof uses neither positivity nor the limit, and a Theorem 13 function satisfies the weaker hypothesis
--   - reading: "an approximation ... with guarantee ρ" → the expected cost of the cheaper of the two outputs is at most ρ times every feasible solution's cost, and every outcome is at least as costly as a feasible solution; reason: Algorithm 2 is randomized and the combination takes the better solution
--   - reading: running time n^{O(1/δ)} → not stated; reason: an O-bound with no constant, as in Theorem 2
--   - encoding: α-approximate TSP, δ-tank step, shortcutting → as in Theorem 2 (tour(U), bestSplit, a feasible solution of no larger cost); reason: same conventions as Theorem 2
--   - generalization: α ≥ 1 → α any real number; reason: as in Theorem 2
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 11, Theorem 14 (with Theorem 13, p. 10, and Corollary 15's proof, p. 11)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

namespace UnsplitCVRP.Combinatorial.Supplement

/-- Theorem 14, p. 11 (inner `min` repaired to `max`): taking the better of Algorithm 2's
output and the solution `B δ'` of Theorem 13 [BTV21] costs, in expectation, at most
`max {3 + f δ', ln 2 + α + (1-δ')/(1-δ)}` times every feasible solution's cost, for every
`δ' ∈ (0, 1)`. -/
theorem theorem_14 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (α : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (tour : Finset (Fin (n + 1)) → List (Fin (n + 1)))
    (htour : ∀ U ⊆ clients n, IsTourOn U (tour U))
    (hctour : ∀ U ⊆ clients n, SupplyChainTheory.routeCost c (tour U) ≤ α * tspOn c U)
    (f : ℝ → ℝ) (B : ℝ → List (List (Fin (n + 1))))
    (hB : ∀ δ', 0 < δ' → δ' < 1 → IsSolution d (B δ'))
    (hBcost : ∀ δ', 0 < δ' → δ' < 1 → ∀ R, IsSolution d R →
      (1 - δ') * SupplyChainTheory.solutionCost c R ≤ radial c d (clients n) →
      SupplyChainTheory.solutionCost c (B δ') ≤ (3 + f δ') * SupplyChainTheory.solutionCost c R) :
    ∀ δ', 0 < δ' → δ' < 1 →
      (∀ S ∈ (configTours d δ).powerset, ∃ R, IsSolution d R ∧
        SupplyChainTheory.solutionCost c R ≤
          min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ∧
      ∀ R, IsSolution d R →
        expect d δ (Real.log 2) xstar
            (fun S => min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ≤
          max (3 + f δ') (Real.log 2 + α + (1 - δ') / (1 - δ)) *
            SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial.Supplement
