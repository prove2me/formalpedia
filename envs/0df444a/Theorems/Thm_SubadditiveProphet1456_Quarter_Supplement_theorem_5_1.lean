-- Prove2me | Theorems.Thm_SubadditiveProphet1456_Quarter_Supplement_theorem_5_1
-- name    : SubadditiveProphet1456.Quarter.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:46:18.890667+00:00
-- url     : https://prove2.me/theorems/1271fab9-741f-4493-851d-3d3a5ee3a60b
-- title:
--   Theorem 5.1 — No online algorithm beats (ρ + η)·LP(1)*, ρ = (e³ − 2e + 1)/(2e³ − 3e + 2) ≈ 0.46004
-- statement:
--   Let
--   $$
--   \rho=\frac{e^3-2e+1}{2e^3-3e+2}\approx0.46004 .
--   $$
--   For every $\eta>0$ there is an input of the online combinatorial allocation problem, with $n$ buyers arriving in a fixed order, $m$ items, and independent finite-support types whose valuations are normalised, monotone and subadditive, such that its ex-ante value $\mathrm{LP}(1)^*$ is positive and every online algorithm $\mathrm{ALG}$ has expected social welfare
--   $$
--   \mathbb E[\mathrm{ALG}]\le(\rho+\eta)\,\mathrm{LP}(1)^*.
--   $$
--   Here $\mathrm{LP}(1)^*$ is the optimum of the ex-ante configuration LP with item capacity $1$, and an online algorithm is any causal, possibly randomized allocation rule with irrevocable decisions: for each type profile it draws an allocation of pairwise disjoint bundles, and the joint law of the bundles of the first buyers depends only on those buyers' types.
--
--   This is the formal version of the paper's impossibility result (Theorem 1.2): against the ex-ante benchmark, no online algorithm is $1/2$-competitive for subadditive buyers, in contrast to the $1/4-\varepsilon$ guarantee of the mission's goal.
--
--   Differences from the source:
--   - encoding: a subadditive valuation input → an Instance n m of the published model (buyers Fin n in arrival order, items Fin m, nonempty finite type supports with positive probabilities, normalized, monotone, subadditive real valuations); reason: the published encoding of the §2 inputs, relabeling only
--   - encoding: every online algorithm → every Policy P with IsOnline P: a law over allocations for each type profile, supported on pairwise disjoint allocations, whose prefix marginals depend only on the observed type prefix; reason: the published model of causal randomized online algorithms, which covers algorithms with internal randomness and memory
--   - reading: an input "with ex-ante value LP(1)*" → the witness additionally satisfies 0 < LP(1)*; reason: the source's instance has LP(1)* > 0 by (29) and divides by it in (30); the stronger reading excludes the all-zero input, which would satisfy the bound vacuously
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, printed p.18, PDF p.19, Theorem 5.1 (formal version of Theorem 1.2, printed p.2, PDF p.3); model §2, printed p.7, PDF p.8.

import Definitions.Def_SubadditiveProphet1456_Quarter_Model

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter.Supplement

/-- STOC 2027 #1456, Theorem 5.1, printed p. 18 (PDF 19), the formal version of Theorem 1.2.
`ρ = (e³ − 2e + 1)/(2e³ − 3e + 2)`. The witness instance must have positive ex-ante value
`LP(1)*`, and the bound is against every causal randomized online policy. -/
theorem theorem_5_1 (η : ℝ) (hη : 0 < η) :
    ∃ (n m : ℕ) (I : Instance n m), 0 < lpValue I 1 ∧
      ∀ P : Policy I, IsOnline I P →
        policyWelfare I P ≤
          ((Real.exp 1 ^ 3 - 2 * Real.exp 1 + 1) / (2 * Real.exp 1 ^ 3 - 3 * Real.exp 1 + 2) + η) *
            lpValue I 1 := by sorry

end SubadditiveProphet1456.Quarter.Supplement
