-- Prove2me | Theorems.Thm_WildeQIT_Recover_hirschman_rectangular_two_one
-- name    : WildeQIT.Recover.hirschman_rectangular_two_one
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-16T01:12:24.682217+00:00
-- url     : https://prove2.me/theorems/25ea59e1-ad17-4282-b8ab-8c9c9028ea02
-- title:
--   Rectangular Schatten 2→1 Hirschman interpolation for Stinespring recovery operators
-- statement:
--   Let $G$ be a function from the complex unit strip to rectangular complex matrices, bounded and continuous on the closed strip and holomorphic in its interior. The finite input and output dimensions are arbitrary and need not agree. For $p>0$, write
--
--   $$\|A\|_p=\left(\operatorname{Tr}[(A^\dagger A)^{p/2}]\right)^{1/p}.$$
--
--   Then, for $0<\theta<1$,
--
--   $$\log\|G(\theta)\|_{2/(1+\theta)}\le\int_{\mathbb R}\left[\alpha_\theta(t)\log\bigl(\|G(it)\|_2^{1-\theta}\bigr)+\beta_\theta(t)\log\bigl(\|G(1+it)\|_1^\theta\bigr)\right]dt.$$
--
--   The logarithm is extended by $\log0=-\infty$, and the right hand side is the signed extended integral defined as the integral of the positive part minus that of the negative part. Rank deficient matrices and zero dimensional index types are included.
--
--   This rectangular specialization supplies exactly the interpolation step for the Stinespring operator family in the quantitative recovery proof. The finite Schatten expression is introduced by a local mathematical abbreviation in the formal statement; its exponents here are strictly positive. The proof reduces to square matrices through a block embedding that preserves these norms.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.2.3 and Eqs.(12.108)–(12.110), p.379; https://arxiv.org/abs/1106.1445v8 . Rectangular extension of the p0=2, p1=1 specialization by zero-block embedding, matching the Stinespring operator in Eq.(12.108).

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
open Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace WildeQIT.Recover
theorem hirschman_rectangular_two_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (G : ℂ → Matrix m n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let normp : ℝ → Matrix m n ℂ → ℝ := fun p A =>
      ((cfc (fun x : ℝ => x^(p/2)) (Aᴴ*A)).trace.re)^(1/p)
    extendedLog (normp (2/(1+θ)) (G θ)) ≤ upperLogIntegral (fun t =>
      (alphaDensity θ t : EReal)*extendedLog ((normp 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
      (betaDensity θ t : EReal)*extendedLog ((normp 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by sorry
end WildeQIT.Recover
