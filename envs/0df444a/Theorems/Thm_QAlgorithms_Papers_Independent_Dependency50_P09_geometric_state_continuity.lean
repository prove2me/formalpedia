-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_geometric_state_continuity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.geometric_state_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:11:00.179666+00:00
-- url     : https://prove2.me/theorems/47c52ba3-2729-4aeb-a9dc-a8a063695374
-- title:
--   Lemma 34
-- statement:
--   Let $\rho$ be a normalized density matrix and $\sigma\ge0$ arbitrary. Set $\widehat\nu=2^{\widehat D_{3/2}(\rho\Vert\sigma)/2}+2^{-\widehat D_{1/2}(\rho\Vert\sigma)/2}+1$. The parameter may be infinite; in that case its strict positive-$\delta$ domain is empty, without applying a finite default to infinity. No support inclusion is assumed.
--
--   $$
--   \widehat\nu\ge3,\qquad\widehat D_{1+\delta}(\rho\Vert\sigma)\le\widehat D(\rho\Vert\sigma)+4\delta(\log_2\widehat\nu)^2\quad\left(0<\delta<\frac{\ln3}{4\ln\widehat\nu}\right).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** PDF p.26 was visually checked: the upper endpoint is open. At sigma=c rho, nu=c^(-1/2)+c^(1/2)+1; at c=1, nu=3 and delta<1/4.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 26, Lemma 34

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Lemma 34, arXiv:2010.01058v3, PDF pp.26,27.
PDF p.26 was visually checked: the upper endpoint is open. At sigma=c rho, nu=c^(-1/2)+c^(1/2)+1; at c=1, nu=3 and delta<1/4. -/
theorem geometric_state_continuity {I : Type} [Fintype I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef) :
    3 ≤ geometricNu rho sigma ∧
      ∀ delta : ℝ, GeometricDelta rho sigma delta →
        geometricD (1+delta) rho sigma ≤ bsD rho sigma +
          ((4*delta*(Real.logb 2 (geometricNu rho sigma).toReal)^2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
