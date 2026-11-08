-- Prove2me | Theorems.Thm_SkewMatching_theorem_2
-- name    : SkewMatching.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:49.231561+00:00
-- url     : https://prove2.me/theorems/a155987b-5f7c-4194-a70a-a3bc3f6a11ca
-- title:
--   Theorem 2 — maximum integral symmetric flow in n^{2+o(1)} time with high probability
-- statement:
--   There is one program $P$ and one function $g(n)\to 0$ such that for every $C>0$ there is a constant $K>0$ with the following property. For every simple skew-symmetric graph $G$ on $n$ vertices, every source $s$, and every listing of the edges of $G$, the probability that $P$ fails to halt within
--
--   $$
--   \lceil K(n+2)^{2+g(n+2)}\rceil
--   $$
--
--   steps with the output encoding a maximum integral symmetric flow from $s$ to $s'$ is at most $(n+2)^{-C}$.
--
--   This is the flow form of the main result, and it implies Theorem 1 through the matching graph.
--
--   Differences from the source:
--   - reading: we can compute → a Machine.Program, a unit-cost word RAM with coins and word bound (n+2)^wordExp; reason: the paper names no machine
--   - reading: n^{2+o(1)} time with high probability → ∃ g → 0 before C, a constant after C, failure probability (n+2)^{−C} for arbitrary C; reason: the paper gives no order; this is the stronger one
--   - encoding: n → n+2 in the time and the failure probability; reason: n = 0, 1 would otherwise be vacuous or junk; implies the printed form for n ≥ 2 up to the constant
--   - reading: simple: no parallel edges between any two vertices → Simple: (tail, head) is injective, so antiparallel pairs and loops are allowed; reason: the wording of p.1 read per ordered pair; §2.3 says the algorithm also handles a constant number of parallel edges, and loops carry only cycle flow
--   - encoding: a simple, directed, skew-symmetric graph → a simple SkewGraph at unit capacity, input as flowMem; reason: unit capacity is the standing assumption of §2.3, p.4; the paper fixes no input format
--   - encoding: compute a maximum integer skew-symmetric flow → when halted, memory cell −1 holds ℓ and cells −2−2j, −3−2j hold the tail and head of the j-th of the ℓ edges with flow 1 of a maximum flow, each edge once (DecodesFlow); reason: the paper fixes no output format; for a Simple graph the ends determine the edge
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 2, p.1, restated p.5

import Mathlib
import Definitions.Def_SkewMatching_DecodesFlow

namespace SkewMatching

open Filter Topology

/-- **Theorem 2**, p.1, restated p.5. "Given a simple, directed, skew-symmetric graph G with n vertices, and two symmetric vertices s and s′, we can compute a maximum integer skew-symmetric flow from s to s′ in n^{2+o(1)} time with high probability."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 2, pp.1, 5.

**Formalization Note.** One program and one `g → 0` before every `C > 0`, then `K`, then the instance. Unit capacity is the standing assumption of §2.3, p.4 and is built into `SkewGraph`. The bad event has outer measure at most `(n+2)^{−C}`. Machine and layout: `Machine.Program` with `W = (n+2)^wordExp`, `flowMem` with the cell of `K` holding `0`, `DecodesFlow`. -/
theorem theorem_2 :
    ∃ (P : Machine.Program) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
        ∀ (n : ℕ) {E : Type} [Fintype E] (G : SkewGraph (Fin n) E), G.Simple →
          ∀ (s : Fin n) (el : List E), IsFullListing el →
            let W := Machine.wordBound P (n + 2)
            let σ₀ := Machine.initState (flowMem G s 0 el)
            Machine.coinTape {τ | ¬ ∃ T ≤ ⌈K * ((n : ℝ) + 2) ^ (2 + g (n + 2))⌉₊,
                Machine.HaltsWithin P W τ σ₀ T ∧
                  ∃ f, G.IsMaxFlow s f ∧ DecodesFlow G (Machine.run P W τ σ₀ T).mem f} ≤
              ENNReal.ofReal (((n : ℝ) + 2) ^ (-C)) := by sorry

end SkewMatching
