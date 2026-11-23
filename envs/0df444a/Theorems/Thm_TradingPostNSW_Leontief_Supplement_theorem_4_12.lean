-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_12
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:42:20.574058+00:00
-- url     : https://prove2.me/theorems/64c311ad-c93a-400a-b8e6-d13dd7632895
-- title:
--   Theorem 4.12, p. 17 (corrected: false clauses refuted) — linear and Leontief counterexamples; full concave purity under enough competition
-- statement:
--   The three clauses of Theorem 4.12 require different outcomes under audit.
--
--   1. The universal linear purity claim is refuted by the explicit three-agent, two-good, perfectly competitive instance of Theorem D.2 (`LinearPurityFails`).
--   2. For concave, non-negative, non-decreasing utilities that are strictly increasing in the product order, with enough competition as in Appendix D.3, every mixed Nash equilibrium of Trading Post without a fee is pure, as in Theorem D.12.
--   3. The Leontief claim for every positive fee is refuted by the all-one two-agent, two-good instance at fee $2$ with budgets one (`LeontiefPurityFails`).
--
--   Mixed strategies are arbitrary independent Borel probability measures and pure profiles have Dirac marginals. The two refutations retain every source assumption; no all-positive-valuation or small-fee restriction is substituted for the source claims.
--
--   Differences from the source:
--   - correction: all Nash equilibria of linear Trading Post with perfect competition are pure → an explicit three-agent, two-good instance satisfying perfect competition and nonempty demands admits a non-pure mixed equilibrium; reason: the printed claim is false: valuations (1,0), (1/10,1), (0,1), budgets 1; the first agent mixes (1,0)/(9/10,1/10), the others bid (0,1); DISPROOF.md checks all deviations. This refutes the source without imposing all-positive valuations
--   - reading: a mild condition of enough competition → enough competition of Appendix D.3 with its non-satiation assumption; reason: p. 17 defers the details to the full version, whose Appendix D.3 states both conditions
--   - generalization: u_i : ℝ^m_+ → ℝ concave, non-negative, non-decreasing and non-satiated, with enough competition at bundles of ℝ^m_+ (Appendix D.3) → concave clause: these conditions only on the box [0,1]^m; reason: every Trading Post allocation lies in the box, so payoffs use only these values; a utility satisfying the conditions on ℝ^m_+ satisfies them on the box, and §2 defines utilities on [0,1]^m
--   - correction: all Nash equilibria of TP(Δ) with Leontief utilities are pure for every Δ > 0 → the two-agent, two-good all-one instance with budgets 1 and fee 2 admits a non-pure mixed equilibrium; reason: no bid reaches the fee and every payoff is zero; DISPROOF.md. The refutation preserves every source assumption and does not discard an unexamined intermediate-fee range
--   - encoding: mixed strategies are probability distributions over S_i (p. 25); equations (20)–(23) write expectations as sums → arbitrary Borel probability measures, admissible almost surely, with product-measure expectations; purity means Dirac marginals; reason: includes discrete and atomless strategies; integrability in IsMixedNE requires the displayed expectations to be actual expectations, not Lean totality values
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 17, Theorem 4.12; Appendix D, pp. 25–30

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_12 :
    LinearPurityFails ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) → EnoughCompetition U →
      ∀ σ : Fin n → MeasureTheory.ProbabilityMeasure (Fin m → ℝ),
        IsMixedNE I U 0 σ → IsPure σ) ∧
    LeontiefPurityFails := by sorry

end TradingPostNSW.Leontief.Supplement
