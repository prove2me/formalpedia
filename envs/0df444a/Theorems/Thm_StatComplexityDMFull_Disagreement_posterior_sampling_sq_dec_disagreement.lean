-- Prove2me | Theorems.Thm_StatComplexityDMFull_Disagreement_posterior_sampling_sq_dec_disagreement
-- name    : StatComplexityDMFull.Disagreement.posterior_sampling_sq_dec_disagreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:56:52.473838+00:00
-- url     : https://prove2.me/theorems/a4c56fcd-3902-4ba3-9f0b-d25ee8f2af71
-- title:
--   Theorem 6.2 — posterior sampling certifies the square-loss dual DEC
-- statement:
--   Let $\mathcal M$ be the discrete model class with measurable bounded mean rewards $f^M:\Pi\to[0,1]$ and selected maximizers $\pi_M$. Let $\mu\in\Delta(\mathcal M)$ be any Radon prior, including countably infinite-support priors. Let $\bar f:\Pi\to[0,1]$ be any measurable external reference mean; it need not be a model-class member or a convex combination. Define the posterior-sampling law $\rho_\mu=(M\mapsto\pi_M)_\#\mu$, the actual objective $J_\gamma$, the prior-dependent dual DEC, and $B_\gamma$ as in the definitions. For every $\gamma\ge e$ the posterior law is an admissible Radon probability law and
--
--   $$\underline{\mathrm{dec}}^{\rm Sq}_\gamma(\mu,\bar f)
--   \le J_\gamma(\mu,\bar f;\rho_\mu)
--   \le\inf_{\Delta>0}\left\{2\Delta+
--   \frac{24\log^2\gamma}{\gamma}\sup_{M\in\mathcal M}
--   \theta(\mathcal F_{\mathcal M}-f^M,\Delta,\gamma^{-1};\rho_\mu)\right\}
--   =B_\gamma(\mu).$$
--
--   The model in the objective and the model used to choose a decision are independent draws from the prior. The displayed chain retains the posterior-sampling certificate as well as its DEC consequence. It is a one-step statement for each prior, rather than a sequential regret guarantee. No finite or discrete decision-space restriction is imposed.
--
--   Differences from the source:
--   - reading: the opening sentence names F while (72) uses the model-induced class FM → the bounded class is the actual meanClass D throughout; reason: p. 5 defines FM from the model class and both (72) and its proof use that class
--   - generalization: reward-observation probability kernels with bounded means and selected maximizers → arbitrary measurable mean data in [0,1] with selected maximizers; reason: each source kernel supplies its bounded measurable expectation and selected optimizer; no other kernel data enter these formulas
--   - encoding: Radon probability laws with the Borel convention and discrete model topology → RadonLaw packages a probability measure and compact inner regularity; source model indices have the discrete topology; reason: these are the source probability class and default model topology, with no support bound or decision-space discreteness
--   - encoding: the law of the selected decision and an independent inner draw → preimage event probabilities and index integrals under the same pushed-forward law; reason: pullbackProb_eq_map proves identification on measurable decision events; discrete model priors also give the canonical atomic probability for arbitrary class events
--   - encoding: suprema and positive-scale infima of the displayed quantities → EReal suprema and infima, with finite objectives embedded from the reals; reason: complete-order extrema do not return spurious real defaults; bounded source classes and positive cutoffs make the displayed extrema finite
--   - encoding: posterior sampling certifies the DEC upper bound → posterior-law probability and Radon admissibility and the explicit DEC-to-objective-to-bound chain; reason: the source witness and its objective are made explicit as conclusions, never assumed as hypotheses
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 45, Theorem 6.2, (72), with (70) and Definition 6.3, (71); proof p. 106

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel
import Definitions.Def_StatComplexityDMFull_Disagreement_Coefficient
import Definitions.Def_StatComplexityDMFull_Disagreement_Objective

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Theorem 6.2 (72), p. 45, with the posterior-sampling certificate and the defined DEC.
The external reference mean need not be in the model class or its convex hull. -/
theorem posterior_sampling_sq_dec_disagreement {M A : Type*}
    [TopologicalSpace M] [DiscreteTopology M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (g : A → ℝ)
    (hg : Measurable g) (hgrange : ∀ a, 0 ≤ g a ∧ g a ≤ 1)
    (γ : ℝ) (hγ : Real.exp 1 ≤ γ) :
    MeasureTheory.IsProbabilityMeasure (posteriorLaw μ.val D.optimal) ∧
    MeasureTheory.Measure.InnerRegular (posteriorLaw μ.val D.optimal) ∧
    sqDEC μ.val D g γ ≤ (sqDecObjective μ.val D g γ (posteriorLaw μ.val D.optimal) : EReal) ∧
    (sqDecObjective μ.val D g γ (posteriorLaw μ.val D.optimal) : EReal) ≤
      posteriorBound μ.val D γ := by sorry

end StatComplexityDMFull.Disagreement
