-- Prove2me | Theorems.Thm_RiskBargaining_proposition_1_counterexample
-- name    : RiskBargaining.proposition_1_counterexample
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:29:29.443983+00:00
-- url     : https://prove2.me/theorems/9dc713a1-860f-4dbb-8dd4-060330f91990
-- title:
--   Appendix A.1, p.34 (corrected: counterexample) — the max in (8) need not exist and $\mathcal U$ need not be compact
-- statement:
--   Let $\Omega=\{1,2,3\}$ with the uniform probability, $p\ge 1$, $\mathcal X$ a point, and two players, with
--   $$
--   \mathcal A_1=\mathcal A_+,\quad\mathcal A_2=\mathcal A_-,\qquad R_1=R_2=1,\qquad M=(11,11,8).
--   $$
--   Both functionals are coherent, continuous, bounded by the expectation and different from it. The instance has positive values and is feasible, but the maximum in (8) does not exist and $\mathcal U(R,M,\mathcal A)$ is not compact.
--
--   So Proposition 1 fails even when $\mathcal A_i\le\mathbb E$, and no rule can satisfy PAR at this instance. This statement is the reason for the attainment condition in the corrected Theorem 1.
--
--   Differences from the source:
--   - correction: since 𝒜_i(M) ≤ E(M), the set is clearly bounded, and the proof concludes that 𝒰(R,M,𝒜) is compact → a feasible instance with 𝒜_i ≤ E on which the max in (8) does not exist and 𝒰 is not compact; reason: the printed proof rests on Lemma 4, which fails at this instance; this item is the refutation
--   - encoding: M : 𝒳 × Ω → ℝ → M : X → Lp ℝ p μ; reason: Assumption 1 makes x ↦ M_x a map into L^p
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.1, proof of Proposition 1, p.34

import Mathlib
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_Feasible
import Definitions.Def_RiskBargaining_Instance_Attained
import Definitions.Def_RiskBargaining_uniformThree
import Definitions.Def_RiskBargaining_discAcceptability

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **Counterexample: Proposition 1 fails and the max in (8) need not exist, even with `𝒜 ≤ E`.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.1, proof of Proposition 1, p.34: "Since 𝒜i(M) ≤ E(M), the set is clearly bounded."

On `Ω = {1, 2, 3}` with the uniform probability, for every `p ≥ 1`, with `X` a point and two players,
take `𝒜_1 = 𝒜_+`, `𝒜_2 = 𝒜_-` of `RiskBargaining.discAcceptability`, `R_1 = R_2 = 1` and `M = (11, 11, 8)`.
Both functionals are coherent (the structure `Instance` asserts it), continuous, bounded by the
expectation, and different from it. The values are positive and the instance is feasible, but the max
in (8) does not exist and `𝒰` is not compact. -/
theorem proposition_1_counterexample (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ I : Instance uniformThree p Unit (Fin 2),
      (∀ i Y, I.A i Y = discAcceptability p (if i = 0 then 1 else -1) Y) ∧
      (∀ i, I.R i = Lp.const p uniformThree 1) ∧
      (∀ (x : Unit) (ω : Fin 3), I.M x ω = ![11, 11, 8] ω) ∧
      (∀ i, 0 < I.v i) ∧ I.Feasible ∧ ¬ I.Attained ∧ ¬ IsCompact I.U ∧
      (∀ i Y, I.A i Y ≤ ∫ ω, Y ω ∂uniformThree) ∧
      (∀ i, Continuous (I.A i)) ∧
      (∀ i, ∃ Y, I.A i Y ≠ ∫ ω, Y ω ∂uniformThree) := by sorry

end RiskBargaining
