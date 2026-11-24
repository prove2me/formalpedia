-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_Supplement_theorem_b2
-- name    : RobustPrefLearn.MTP.Supplement.theorem_b2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:14:17.144515+00:00
-- url     : https://prove2.me/theorems/7842abbd-6634-4516-8ab7-483b977bec3e
-- title:
--   Appendix B.2 theorem — general lower bounds (corrected: δ ≤ 1/2)
-- statement:
--   Let $\Theta$, $\mathcal S$, $\mathcal X$ be arbitrary parameter, experiment and outcome spaces, with finitely many hypotheses $H_i\subseteq\Theta$. Assume every parameter has a true hypothesis and that all experiment laws are positive normalized probability masses, with distinct parameters identifiable by some experiment and outcome (Assumptions 1–2). Define $A(\theta)$ by disjoint true-hypothesis sets and $I_*(\theta)$ by (26)–(27). For every $\theta$ with $I_*(\theta)>0$:
--
--   1. Every $\delta$-accurate policy $\pi$ satisfies, for $0<\delta\le1/2$,
--   $$\mathbb E_\theta^\pi[\tau]\ge\frac{\mathrm{kl}(\delta,1-\delta)}{I_*(\theta)}.$$
--   2. Every accurate family $\Pi=(\pi_\delta)_{0<\delta<1}$ satisfies
--   $$\liminf_{\delta\downarrow0}\frac{\mathbb E_\theta^{\pi_\delta}[\tau]}{\log(1/\delta)}\ge\frac1{I_*(\theta)}.$$
--   Here $\mathrm{kl}(a,b)=a\log(a/b)+(1-a)\log((1-a)/(1-b))$. Accuracy requires almost-sure termination and error at most $\delta$ at every parameter.
--
--   This general lower bound permits overlapping composite hypotheses and arbitrary discrete experiment spaces. It contains the consumer-preference lower bound as a specialization.
--
--   **Formalization Note** Both clauses are retained in one item. The finite-confidence domain is corrected because the printed extension to $\delta>1/2$ is false; the counterexample and failed extension on p.46 are retained in DISPROOF.md. No finiteness, countability or integrability premise is added. The nonnegative-series KL and expectations take values in $[0,\infty]$, and division by infinite information gives zero.
--
--   Differences from the source:
--   - correction: 0<delta<1 for the nonasymptotic inequality → 0<delta<=1/2 for that inequality; the family still ranges over 0<delta<1; reason: the p.46 separation argument applies only up to 1/2; a one-observation binary experiment refutes the extension at delta=0.99 (DISPROOF.md)
--   - reading: liminf for an implicitly delta-indexed policy → liminf for every accurate family, along the right neighborhood of zero; reason: a limit in delta requires a family of policies; this keeps the whole asymptotic conclusion
--   - encoding: signed sum defining KL on arbitrary outcomes and probability laws on histories → nonnegative corrected KL series and explicit product history law, with ENNReal series; reason: normalization cancels -f+g; the representation retains infinite divergences and expectations without a nonsummable real-tsum default
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Theorem (unnumbered, Appendix B.2, PDF 45), p. 45; source.pdf sha256 5c09534e5696bccabf34ab8a3582c3ade8e448db308c84ee4895a5961f8629f1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Model
import Definitions.Def_RobustPrefLearn_MTP_Supplement_Information

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP.Supplement

universe u v w

/-- Appendix B.2, p.45, both clauses. Corrected finite-confidence domain:
0 < δ ≤ 1/2 (the printed extension to δ near 1 is false; p.46 only establishes
separation for δ ≤ 1/2). Arbitrary parameter, experiment and outcome types.
The asymptotic statement is about every accurate δ-indexed family. -/
theorem theorem_b2 {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (hH : HasTrueHypothesis M)
    (hM : TestingAssumptions M) (θ : Θ) (hinfo : 0 < testingInfo M θ) :
    (∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 → ∀ π : TestingPolicy S X I,
      TestingDeltaAccurate M δ π →
        ENNReal.ofReal (kl δ (1 - δ)) / testingInfo M θ ≤ testingExpTau M π θ) ∧
    (∀ fam : ℝ → TestingPolicy S X I, TestingAccurate M fam →
      (testingInfo M θ)⁻¹ ≤ testingLowerRate M fam θ) := by sorry

end RobustPrefLearn.MTP.Supplement
