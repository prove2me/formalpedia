-- Prove2me | Theorems.Thm_StatComplexityDMFull_Disagreement_decoupling_disagreement
-- name    : StatComplexityDMFull.Disagreement.decoupling_disagreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:55:29.989078+00:00
-- url     : https://prove2.me/theorems/955289a7-ffe5-45d9-ae3f-78df06e589a7
-- title:
--   Lemma E.2 — disagreement decoupling for all Radon index laws
-- statement:
--   Let $\mathcal Z$ be an index space, $\Pi$ a decision space, $\mu\in\Delta(\mathcal Z)$ a Radon Borel probability law, and $\mathcal F\subseteq(\Pi\to[-R,R])$ for any $R\ge0$. Choose $f_z\in\mathcal F$ and $\pi_z\in\Pi$ for each $z$, and let $\rho_\mu=(z\mapsto\pi_z)_\#\mu$. The selection map is measurable, the squared sections, absolute diagonal and squared independent-cross evaluations are almost everywhere measurable, and the disagreement-event preimages at positive scales are measurable in the completed index law. For every $\gamma>0$,
--
--   $$\mathbb E_{z\sim\mu}|f_z(\pi_z)|\le
--   \inf_{\Delta>0}\left\{2\Delta+
--   \frac{6\theta(\mathcal F,\Delta,\gamma^{-1};\rho_\mu)\log^2(\max\{R\gamma,e\})}{\gamma}\right\}
--   +\gamma\mathbb E_{z\sim\mu}\mathbb E_{z'\sim\mu}f_z(\pi_{z'})^2.$$
--
--   The left side couples the same index to its function and decision. The quadratic term uses independent indices. This is the generic decoupling result used by the posterior-sampling theorem. No maximizing property, finite support, countable function class, or lower bound $R\ge1$ is imposed. The radius-zero case is included.
--
--   **Formalization Note** The bounded random variables and the stated measurability convention give genuine integrable expectations; no nonintegrable integral default is used. All logarithms are natural and $e=\exp(1)$.
--
--   Differences from the source:
--   - encoding: ordinary expectations and probabilities of all displayed random variables and events → explicit AE strong measurability of squared sections, absolute diagonal and squared independent-cross evaluations; measurable selection and null-measurable positive-scale event preimages; reason: this spells out the ordinary source probability convention and boundedness ensures integrability without requiring a countable class
--   - encoding: the symmetric bounded range [-R,R] → a nonnegative real radius R including zero; reason: a negative radius admits no function-decision family under a probability law; every nonvacuous source instance has R nonnegative
--   - encoding: the law of the selected decision and an independent inner draw → preimage event probabilities and index integrals under the same pushed-forward law; reason: pullbackProb_eq_map proves identification on measurable decision events; discrete model priors also give the canonical atomic probability for arbitrary class events
--   - encoding: suprema and positive-scale infima of the displayed quantities → EReal suprema and infima, with finite objectives embedded from the reals; reason: complete-order extrema do not return spurious real defaults; bounded source classes and positive cutoffs make the displayed extrema finite
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 104, Lemma E.2, (140); standing setup Section E.2.1; proof pp. 104–106

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_Coefficient

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Lemma E.2 (140), p. 104, including every nonnegative radius and every Radon index law.
The measurability hypotheses concern the absolute/squared evaluations and positive-scale events;
boundedness then ensures genuine integrability of every displayed expectation. -/
theorem decoupling_disagreement {Z A : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace A]
    (μ : RadonLaw Z) (F : Set (A → ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hF : ∀ f ∈ F, ∀ a, |f a| ≤ R)
    (fz : Z → A → ℝ) (hfz : ∀ z, fz z ∈ F) (a : Z → A) (ha : Measurable a)
    (hsections : ∀ f ∈ F, MeasureTheory.AEStronglyMeasurable (fun z => (f (a z)) ^ 2) μ.val)
    (hdiag : MeasureTheory.AEStronglyMeasurable (fun z => |fz z (a z)|) μ.val)
    (hcross : MeasureTheory.AEStronglyMeasurable (fun zz : Z × Z => (fz zz.1 (a zz.2)) ^ 2)
      (μ.val.prod μ.val))
    (hevents : ∀ d s : ℝ, 0 < d → 0 < s → MeasureTheory.NullMeasurableSet
      (a ⁻¹' disagreementEvent μ.val a F d s) μ.val)
    (γ : ℝ) (hγ : 0 < γ) :
    ((∫ z, |fz z (a z)| ∂μ.val : ℝ) : EReal) ≤
      (⨅ Δ : {x : ℝ // 0 < x}, ((2 * Δ.val : ℝ) : EReal) +
        ((6 * Real.log (max (R * γ) (Real.exp 1)) ^ 2 / γ : ℝ) : EReal) *
          disagreementCoeff μ.val a F Δ.val γ⁻¹) +
      ((γ * (∫ z, (∫ z', (fz z (a z')) ^ 2 ∂μ.val) ∂μ.val) : ℝ) : EReal) := by sorry

end StatComplexityDMFull.Disagreement
