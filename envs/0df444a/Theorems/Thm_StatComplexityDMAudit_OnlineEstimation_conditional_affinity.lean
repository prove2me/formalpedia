-- Prove2me | Theorems.Thm_StatComplexityDMAudit_OnlineEstimation_conditional_affinity
-- name    : StatComplexityDMAudit.OnlineEstimation.conditional_affinity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:05:35.072689+00:00
-- url     : https://prove2.me/theorems/1bf461b3-f2f0-41da-9641-d7e579337e73
-- title:
--   §A.3.5, proof of Lemma A.14 — conditional-affinity display
-- statement:
--   In the realizable protocol, fix a round $t$ and write $p(y)=g_{i^\star,t}(y\mid x_t;H_{<t})$, $q(y)=\widehat g_t(y\mid x_t;H_{<t})$, and $X_t=(\ell_{\log,t}(\widehat g_t)-\ell_{\log,t}(g_{i^\star,t}))/2$. Then almost surely, with all conditional expectations conditioned on $(H_{<t},x_t)$,
--   $$\mathbb E[e^{-X_t}\mid H_{<t},x_t]=\mathbb E[\sqrt{q(y_t)/p(y_t)}\mid H_{<t},x_t]=\int_Yp(y)\sqrt{q(y)/p(y)}\,\nu(dy\mid x_t)=\int_Y\sqrt{p(y)q(y)}\,\nu(dy\mid x_t)=1-\tfrac12D_{\mathrm H}^2(p,q).$$
--   The ratio is zero off the true support. The half loss gap is extended-real: when the learner predicts zero on the true support, it is $+\infty$ and $e^{-X_t}=0$. All densities are finite, normalized and jointly measurable; the base kernel is only fibrewise sigma-finite.
--
--   This target retains the full conditional-expectation and integral chain on the source's general domain, rather than just its finite-vector algebraic specialization. Realizability is the conditional outcome-law assumption, not the displayed conclusion.
--
--   Differences from the source:
--   - encoding: rounds 1 through T → Fin T with round t.val corresponding to source round t.val + 1; reason: the order, preceding histories and finite sums are identical
--   - encoding: the true conditional outcome law given the past and current context → conditional integral identities for every nonnegative jointly measurable test function; reason: this is the integral formulation of Assumption A.1 on the given probability space, without a regular-disintegration assumption
--   - encoding: the conditional-affinity display and its likelihood ratio → almost-sure equality of the full chain, with zero extension off the true support and extended exponential/log loss; reason: conditional expectations are defined up to null sets; realizability makes the true density positive at the observed outcome almost surely and zero learner densities remain allowed
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, §A.3.5, proof of Lemma A.14, unnumbered conditional-affinity display, printed/PDF p. 79; setup pp. 75–76; equation (5), p. 10.

import Mathlib
import Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Performance

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- arXiv:2112.13487v3, §A.3.5, proof of Lemma A.14, p. 79, unnumbered
conditional-affinity display. All links of the displayed chain are retained;
the half loss gap is extended-real when the learner predicts zero. -/
theorem conditional_affinity {Ω I X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}
    (ν : Kernel X Y) (hν : ∀ x, SigmaFinite (ν x))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Observations Ω X Y T)
    (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar) (t : Fin T) :
    ∀ᵐ ω ∂μ,
      condLExp (o.current t) μ
          (fun a => EReal.exp (-(roundGap o q g istar t a / 2))) ω =
        condLExp (o.current t) μ
          (fun a => sqrtRatio (densityAt o (g istar) t a (o.obs t a).2)
            (densityAt o q t a (o.obs t a).2)) ω ∧
      condLExp (o.current t) μ
          (fun a => sqrtRatio (densityAt o (g istar) t a (o.obs t a).2)
            (densityAt o q t a (o.obs t a).2)) ω =
        (∫⁻ y, (densityAt o (g istar) t ω y : ℝ≥0∞) *
          sqrtRatio (densityAt o (g istar) t ω y) (densityAt o q t ω y)
          ∂ν ((o.obs t ω).1)) ∧
      (∫⁻ y, (densityAt o (g istar) t ω y : ℝ≥0∞) *
          sqrtRatio (densityAt o (g istar) t ω y) (densityAt o q t ω y)
          ∂ν ((o.obs t ω).1)) =
        affinity (ν ((o.obs t ω).1)) (densityAt o (g istar) t ω) (densityAt o q t ω) ∧
      (affinity (ν ((o.obs t ω).1)) (densityAt o (g istar) t ω)
          (densityAt o q t ω) : EReal) =
        1 - (roundHellinger o q g istar t ω : EReal) / 2 := by sorry

end StatComplexityDMAudit.OnlineEstimation
