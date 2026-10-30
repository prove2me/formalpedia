-- Prove2me | Theorems.Thm_StatComplexityDMFull_Disagreement_sq_shift_le_four
-- name    : StatComplexityDMFull.Disagreement.sq_shift_le_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:54:23.329186+00:00
-- url     : https://prove2.me/theorems/4d54e916-12d6-461b-a859-e2c5e6b32c11
-- title:
--   §E.2.2 — the full independent squared-error comparison
-- statement:
--   Let $\mu$ be any Radon prior on the discrete model class, and let $f^M:\Pi\to[0,1]$ be its mean-reward data. Fix a decision $\pi\in\Pi$ and a reference value $\bar f(\pi)\in\mathbb R$. For independent $M,\widetilde M\sim\mu$,
--
--   $$\mathbb E_M\mathbb E_{\widetilde M}(f^M(\pi)-f^{\widetilde M}(\pi))^2
--   \le2\mathbb E_M(f^M(\pi)-\bar f(\pi))^2
--   +2\mathbb E_{\widetilde M}(\bar f(\pi)-f^{\widetilde M}(\pi))^2
--   =4\mathbb E_M(f^M(\pi)-\bar f(\pi))^2.$$
--
--   The statement retains both the comparison and the equality in the source display. It relates the independent-copy squared error to the squared error against the external reference. Expectations use the entire prior, including infinite support.
--
--   Differences from the source:
--   - generalization: reward-observation probability kernels with bounded means and selected maximizers → arbitrary measurable mean data in [0,1] with selected maximizers; reason: each source kernel supplies its bounded measurable expectation and selected optimizer; no other kernel data enter these formulas
--   - encoding: Radon probability laws with the Borel convention and discrete model topology → RadonLaw packages a probability measure and compact inner regularity; source model indices have the discrete topology; reason: these are the source probability class and default model topology, with no support bound or decision-space discreteness
--   - generalization: the reference mean belongs to [0,1] → the fixed reference value may be any real number; reason: only a fixed value is used, its squared errors remain bounded in the model variable, and every source reference is included
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 106, Section E.2.2, first displayed squared-error inequality in the proof of Theorem 6.2 (unnumbered)

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- Section E.2.2, first squared-error display, p. 106; both the inequality and equality. -/
theorem sq_shift_le_four {M A : Type*} [TopologicalSpace M] [DiscreteTopology M]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (g : A → ℝ) (a : A) :
    (∫ m, (∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val) ∂μ.val) ≤
      2 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) +
      2 * (∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) ∧
    2 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) +
      2 * (∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) =
      4 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) := by sorry

end StatComplexityDMFull.Disagreement
