-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_uniform_seed_mixture_integral
-- name    : PandoraBO.Private20261023.uniform_seed_mixture_integral
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:47.065699+00:00
-- url     : https://prove2.me/theorems/167c1fbc-2322-46c0-abcc-2415e15245f2
-- title:
--   Integration under a rescaled uniform randomization seed
-- statement:
--   Let μ be a sigma-finite-in-the-S-finite-sense measure, and let the seed be uniformly distributed on [0,1], independently of the first coordinate. Let 0<a<1 and let f, g, and F be integrable under the product law, where F uses f(x,u/a) when u≤a and g(x,(u−a)/(1−a)) otherwise. Then the integral of F is a times the integral of f plus (1−a) times the integral of g. This change-of-variables identity supplies the randomization step for policy mixtures.
-- source:
--   Auxiliary construction for Xie et al., Cost-aware Bayesian Optimization via the Pandora’s Box Gittins Index, author revised manuscript reviewed 23 October 2026, Appendix B.5, Lemmas 7–8 and Theorem 2. This result isolates the measurable-policy existence or policy-randomization step; it is not a verbatim numbered claim.

import Definitions.Def_PandoraBO_Model
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory PandoraBO
set_option autoImplicit false

theorem PandoraBO.Private20261023.uniform_seed_mixture_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f g F : X × ℝ → ℝ)
    (hformula : ∀ x u, F (x, u) =
      if u ≤ a then f (x, u / a) else g (x, (u - a) / (1 - a)))
    (hf : Integrable f (μ.prod PandoraBO.seedLaw))
    (hg : Integrable g (μ.prod PandoraBO.seedLaw))
    (hF : Integrable F (μ.prod PandoraBO.seedLaw)) :
    (∫ ω, F ω ∂μ.prod PandoraBO.seedLaw) =
      a * (∫ ω, f ω ∂μ.prod PandoraBO.seedLaw) +
        (1 - a) * (∫ ω, g ω ∂μ.prod PandoraBO.seedLaw) := by sorry
