-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_convexity_and_comparison
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.convexity_and_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:55:39.181292+00:00
-- url     : https://prove2.me/theorems/90012eea-b347-4247-99eb-deafe24a218c
-- title:
--   Convexity, roof attainment and squared-concurrence comparison
-- statement:
--   Let $\rho,\sigma$ be density operators on any fixed bipartite system with positive finite local dimensions and let $p\in[0,1]$. Write $C$ for mixed I-concurrence and $\tau$ for the separate pure-tangle convex roof. Each of $E=C$, $E=C^2$, and $E=\tau$ satisfies
--
--   $$
--   E(p\rho+(1-p)\sigma)\le pE(\rho)+(1-p)E(\sigma),
--   \qquad 0\le C(\rho),\qquad C(\rho)^2\le\tau(\rho).
--   $$
--
--   For each $\rho$ there is a finite normalized pure-state ensemble representing $\rho$ that attains $C(\rho)$ as its average pure concurrence, and there is such an ensemble attaining $\tau(\rho)$ as its average pure tangle. The two optimizing ensembles need not coincide.
--
--   This records the minimum convention of the roofs and distinguishes convexity of squared concurrence from the source's unasserted LOCC monotonicity of that square.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 5, §2: convexity and squared-concurrence versus tangle

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Section 2, and p.3, (1.4)--(1.5): convexity of concurrence,
its square and tangle; C(rho)^2<=tau(rho); both roofs attain their minima.
No LOCC claim is made for squared mixed concurrence. -/
theorem convexity_and_comparison :
    Frontier30.P30.IsConvex (fun _ _ rho => concurrence rho) ∧
    Frontier30.P30.IsConvex (fun _ _ rho => concurrence rho ^ 2) ∧
    Frontier30.P30.IsConvex (fun _ _ rho => tangle rho) ∧
    ∀ a b : ℕ, ∀ ha : 0 < a, ∀ hb : 0 < b,
      ∀ rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, IsDensityMatrix rho →
        0 ≤ concurrence rho ∧ concurrence rho ^ 2 ≤ tangle rho ∧
        (∃ e : PureEnsemble (Fin a × Fin b), IsOptimalPureEnsemble pureConcurrence rho e) ∧
        (∃ e : PureEnsemble (Fin a × Fin b), IsOptimalPureEnsemble pureTangle rho e) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
