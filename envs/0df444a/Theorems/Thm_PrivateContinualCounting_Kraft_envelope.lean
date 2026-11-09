-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_envelope
-- name    : PrivateContinualCounting.Kraft.envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:04.969227+00:00
-- url     : https://prove2.me/theorems/cf817584-ccd3-4f57-bbbf-1f591ef3e251
-- title:
--   Lemma 3.4 — the explicit uniform envelope constant
-- statement:
--   Fix $D\ge1$. For every real nondecreasing $g:[1,\infty)\to[1,\infty)$ with doubling constant $D$ satisfying the construction preamble $K(g)$, use its canonical weight $f$. For every integer $t\ge3$,
--   $$\int F_tf\,dm\le C_D(\ln t)^2g(\ln t),$$
--   where $C_D>0$ depends only on $D$. The paper's displayed $C_D$ (the $O_D(\cdot)$ envelope) is instantiated by its own Appendix C proof:
--   $$q=\frac{\ln D}{\ln2},\quad \Gamma_q=\int_0^\infty e^{-2s}(1+s)^{q+1}\,ds,\qquad
--   C_D=\frac{D\Gamma_q}{\pi}+\frac\pi2+\frac{\pi^2e}{(\ln3)^2}.$$
--   The theorem includes integrability of the defining $\Gamma_q$ integrand and of $F_tf$. One constant works for every admissible $g$ and time for the chosen $D$; no $g(1)$ or horizon is hidden in it. The construction preamble is preserved, so this is not the optional generalization dropping Kraft summability. This is the analytic estimate used for the scalar sufficiency bound.
--
--   Differences from the source:
--   - encoding: g defined on the real half-line [1,∞) → g is a function on ℝ with every envelope condition restricted to [1,∞); reason: Values below 1 are unused in all claims; monotonicity and doubling allow discontinuities.
--   - encoding: C_D depending only on D → the exact displayed Appendix C constant, with convergence and positivity explicit; reason: The source proof supplies all three terms; fixing D before g and t makes its stated uniformity binding.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, Lemma 3.4 (envelope), with §3.3 preamble; Kisung Park, STOC 2027 submission #86 (October 2026), p. 20, PDF p. 22, Appendix C, proof of Lemma 3.4, regions (a)–(c)

import Definitions.Def_PrivateContinualCounting_Kraft_SpectralConstruction

open MeasureTheory

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Lemma 3.4 with Appendix C's explicit constant, uniform in g and t for each D.
The construction's Kraft preamble is retained. -/
theorem envelope (D : ℝ) (hD : 1 ≤ D) :
    IntegrableOn (fun s : ℝ => Real.exp (-2 * s) *
      Real.rpow (1 + s) (Real.log D / Real.log 2 + 1)) (Set.Ici 0) ∧
    0 < envelopeConstant D ∧
    ∀ (g : ℝ → ℝ), IsEnvelopeWith g D → KraftCondition g →
      ∀ t : ℕ, 3 ≤ t →
        Integrable (fun θ => prefixKernel t θ * spectralWeight g θ) circleMeasure ∧
        (∫ θ, prefixKernel t θ * spectralWeight g θ ∂circleMeasure) ≤
          envelopeConstant D * (Real.log (t : ℝ)) ^ 2 * g (Real.log (t : ℝ)) := by sorry

end PrivateContinualCounting.Kraft
