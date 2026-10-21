-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_boundaryRateDivergence
-- name    : QAlgorithms.Papers.Independent.Next46.P27.boundaryRateDivergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:23:52.518135+00:00
-- url     : https://prove2.me/theorems/3e740818-d20d-4a8c-87cb-7b49f6cc5ba3
-- title:
--   Boundary entropy-production rates diverge
-- statement:
--   Let $\rho$ be a density on the full single-mode Fock space with finite entropy $S(\rho)$ in nats. Assume $\rho$ has a nonzero kernel: there is $u\ne0$ with $\rho u=0$. For $\gamma>0$ and the exact noise channel $\Phi_{\gamma t}$,
--
--   $$\lim_{t\downarrow0}\frac{S(\Phi_{\gamma t}(\rho))-S(\rho)}{t}=+\infty,\qquad R_\gamma(\rho)=+\infty.$$
--
--   Here $R_\gamma$ is the lower right Dini rate. The first assertion is a genuine right limit in the extended nonnegative reals, and is stronger than merely assigning the liminf an infinite value. This formalizes the boundary-rate conclusion without asserting a finite-time entropy maximum.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 3, Section III: boundary entropy-rate divergence

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.3, Section III: boundary means a nonzero kernel, not the topological
boundary of the infinite positive cone. Finite input entropy prevents infinity-minus-infinity. -/
theorem boundaryRateDivergence (gamma : ℝ) (hgamma : 0 < gamma)
    (rho : B.FockOperator) (hrho : B.IsDensity rho) (hentropy : A.fockEntropyNats rho < ⊤)
    (hboundary : ∃ u : B.Fock, u ≠ 0 ∧ rho u = 0) :
    Tendsto (entropyQuotient gamma rho) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 ⊤) ∧
      entropyRate gamma rho = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
