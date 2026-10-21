-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_displacementOrbitOfLocalMinima
-- name    : QAlgorithms.Papers.Independent.Next46.P27.displacementOrbitOfLocalMinima
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:25:10.80863+00:00
-- url     : https://prove2.me/theorems/8dcd44aa-0da3-4a7c-b022-a444eda436aa
-- title:
--   Continuous displacement orbits of local entropy minima
-- statement:
--   Let $v>0$ and let $\rho$ be a finite-entropy density that locally minimizes $S(\Phi_v(X))$ among densities with $S(X)=S(\rho)$, using trace-norm neighborhoods. For $\alpha\in\mathbb C$ write $\rho_\alpha=D(\alpha)\rho D(\alpha)^\dagger$. The map $\alpha\mapsto\rho_\alpha$ is continuous in trace norm, every $\rho_\alpha$ is another constrained local minimum, and
--
--   $$S(\rho_\alpha)=S(\rho),\qquad S(\Phi_v(\rho_\alpha))=S(\Phi_v(\rho)).$$
--
--   Every two orbit points are joined by a trace-norm continuous path lying entirely in this orbit. This is the connected continuous family of local minima described in Section II; no smooth embedded-manifold claim is added.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 2, Section II: displacement orbit of entropy minima

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.2–3: the whole continuous displacement orbit has the same entropy
and consists of local minima. Straight phase-space segments give paths between
any two orbit points, so this is a connected orbit, without a smooth-manifold claim. -/
theorem displacementOrbitOfLocalMinima (v : ℝ) (hv : 0 < v)
    (rho : B.FockOperator) (hlocal : LocalOutputMinimum v rho) :
    TraceContinuous (orbitPoint rho) ∧
    (∀ alpha : ℂ, LocalOutputMinimum v (orbitPoint rho alpha) ∧
      A.fockEntropyNats (orbitPoint rho alpha) = A.fockEntropyNats rho ∧
      A.fockEntropyNats (A.displacementNoiseChannel v (orbitPoint rho alpha)) =
        A.fockEntropyNats (A.displacementNoiseChannel v rho)) ∧
    ∀ alpha beta : ℂ, ∃ p : Set.Icc (0 : ℝ) 1 → B.FockOperator,
      TraceContinuous p ∧ p ⟨0, by constructor <;> norm_num⟩ = orbitPoint rho alpha ∧
      p ⟨1, by constructor <;> norm_num⟩ = orbitPoint rho beta ∧
      ∀ t, ∃ z : ℂ, p t = orbitPoint rho z := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
