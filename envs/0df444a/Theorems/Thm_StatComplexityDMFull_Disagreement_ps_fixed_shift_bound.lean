-- Prove2me | Theorems.Thm_StatComplexityDMFull_Disagreement_ps_fixed_shift_bound
-- name    : StatComplexityDMFull.Disagreement.ps_fixed_shift_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:56:06.222934+00:00
-- url     : https://prove2.me/theorems/3b02e645-9050-4ac7-ba85-386ae65be811
-- title:
--   §E.2.2 — the final fixed-shift inequality
-- statement:
--   Let $\mu$ be a Radon prior over the discrete model class, with means $f^M:\Pi\to[0,1]$ and selected maximizers $\pi_M$. Put $p=\rho_\mu=(M\mapsto\pi_M)_\#\mu$. Fix a comparison model $\widetilde M\in\mathcal M$, outside all expectations. For every $\gamma\ge e$,
--
--   $$\mathbb E_{M\sim\mu}[f^M(\pi_M)-f^{\widetilde M}(\pi_M)]\le
--   \inf_{\Delta>0}\left\{2\Delta+
--   \frac{24\theta(\mathcal F_{\mathcal M}-f^{\widetilde M},\Delta,\gamma^{-1};\rho_\mu)
--   \log^2(\max\{\gamma,e\})}{\gamma}\right\}
--   +\frac\gamma4\mathbb E_{\pi\sim p}\mathbb E_{M\sim\mu}(f^M(\pi)-f^{\widetilde M}(\pi))^2.$$
--
--   The coefficient uses the entire shifted model-induced class, and the infimum uses every positive scale. The independent error term is averaged in the decision-first order printed on the page. This result is the final fixed-comparison display used in the proof of Theorem 6.2.
--
--   Differences from the source:
--   - generalization: reward-observation probability kernels with bounded means and selected maximizers → arbitrary measurable mean data in [0,1] with selected maximizers; reason: each source kernel supplies its bounded measurable expectation and selected optimizer; no other kernel data enter these formulas
--   - encoding: Radon probability laws with the Borel convention and discrete model topology → RadonLaw packages a probability measure and compact inner regularity; source model indices have the discrete topology; reason: these are the source probability class and default model topology, with no support bound or decision-space discreteness
--   - encoding: the law of the selected decision and an independent inner draw → preimage event probabilities and index integrals under the same pushed-forward law; reason: pullbackProb_eq_map proves identification on measurable decision events; discrete model priors also give the canonical atomic probability for arbitrary class events
--   - encoding: suprema and positive-scale infima of the displayed quantities → EReal suprema and infima, with finite objectives embedded from the reals; reason: complete-order extrema do not return spurious real defaults; bounded source classes and positive cutoffs make the displayed extrema finite
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 106, Section E.2.2, final displayed fixed-shift inequality in the proof of Theorem 6.2 (unnumbered)

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel
import Definitions.Def_StatComplexityDMFull_Disagreement_Coefficient

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Section E.2.2, final display, p. 106. The comparison model is fixed, outside all integrals. -/
theorem ps_fixed_shift_bound {M A : Type*} [TopologicalSpace M] [DiscreteTopology M]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (n : M)
    (γ : ℝ) (hγ : Real.exp 1 ≤ γ) :
    ((∫ m, D.mean m (D.optimal m) - D.mean n (D.optimal m) ∂μ.val : ℝ) : EReal) ≤
      (⨅ Δ : {x : ℝ // 0 < x}, ((2 * Δ.val : ℝ) : EReal) +
        ((24 * Real.log (max γ (Real.exp 1)) ^ 2 / γ : ℝ) : EReal) *
          disagreementCoeff μ.val D.optimal (shiftClass (meanClass D) (D.mean n)) Δ.val γ⁻¹) +
      ((γ / 4 * (∫ a, (∫ m, (D.mean m a - D.mean n a) ^ 2 ∂μ.val)
        ∂(posteriorLaw μ.val D.optimal)) : ℝ) : EReal) := by sorry

end StatComplexityDMFull.Disagreement
