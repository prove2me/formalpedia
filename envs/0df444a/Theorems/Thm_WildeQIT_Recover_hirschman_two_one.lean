-- Prove2me | Theorems.Thm_WildeQIT_Recover_hirschman_two_one
-- name    : WildeQIT.Recover.hirschman_two_one
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-16T00:58:18.959428+00:00
-- url     : https://prove2.me/theorems/e53451f0-0d5a-4d0a-9555-527ac8e2b74d
-- title:
--   Stein–Hirschman interpolation from Schatten 2 to Schatten 1 for quantitative recovery
-- statement:
--   Let $G$ be a matrix valued function on the complex strip, bounded and continuous on $0\le\operatorname{Re}z\le1$ and holomorphic on $0<\operatorname{Re}z<1$. The matrices act on an arbitrary finite dimensional complex space, and the zero dimensional case is included. For $0<\theta<1$ set $p_\theta=2/(1+\theta)$. Then
--
--   $$\log\|G(\theta)\|_{p_\theta}\le\int_{\mathbb R}\left[\alpha_\theta(t)\log\bigl(\|G(it)\|_2^{1-\theta}\bigr)+\beta_\theta(t)\log\bigl(\|G(1+it)\|_1^\theta\bigr)\right]dt.$$
--
--   Here $\|\cdot\|_2$ is the Hilbert–Schmidt norm, $\|\cdot\|_1$ is the trace norm, and $\alpha_\theta,\beta_\theta$ are the registered Hirschman probability densities. Logarithms are extended by $\log0=-\infty$, and the right hand side uses the signed extended integral of the positive part minus the negative part.
--
--   This is the $p_0=2$, $p_1=1$ specialization of Stein–Hirschman interpolation used directly in the proof of the quantitative quantum recovery bound. The formalization uses the registered Schatten norm defined by real continuous functional calculus on $A^\dagger A$ and represents $p_\theta$ as a finite extended nonnegative real. It does not claim the arbitrary endpoint version.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.2.3 and §12.5, p.379, Eqs.(12.108)–(12.110), https://arxiv.org/abs/1106.1445v8 . The specialization p0=2, p1=1 is the one explicitly used in the recovery proof. See also Junge–Renner–Sutter–Wilde–Winter, arXiv:1509.07127, Lemma 3.2 and Appendix A.

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
open Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace WildeQIT.Recover
theorem hirschman_two_one {n : Type*} [Fintype n] [DecidableEq n] (G : ℂ → Matrix n n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (schattenNorm (ENNReal.ofReal (2/(1+θ))) (G θ)) ≤
      upperLogIntegral (fun t =>
        (alphaDensity θ t : EReal)*extendedLog ((schattenNorm 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
        (betaDensity θ t : EReal)*extendedLog ((schattenNorm 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by sorry
end WildeQIT.Recover
