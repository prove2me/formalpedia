-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_main_cloning_region
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.main_cloning_region
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:19:17.483959+00:00
-- url     : https://prove2.me/theorems/2548c14d-93f3-44a1-85b4-e0edd0a6fa77
-- title:
--   Complete asymmetric cloning region
-- statement:
--   Let $d\ge2$ be the qudit dimension. A pair $(p,q)$ is achievable when a complex-linear CPTP channel from one qudit to two ordered qudits has marginal maps $D_p,D_q$, where $D_p(X)=pX+(1-p)\operatorname{Tr}(X)I/d$. Set $s=p+q$, $t=p-q$, $a=(d^2-1)^{-1/2}$, $b=(d^2-1)^{-1}$ and $c_\lambda=(\lambda d-2)/(d^2-1)$. Then
--
--   $$
--   (p,q)\text{ is achievable}\quad\Longleftrightarrow\quad
--   \exists\lambda\in[0,d],\ \frac{t^2}{a^2}+\frac{(s-c_\lambda)^2}{b^2}\le\lambda^2.
--   $$
--
--   For constant squared pure-input fidelities $(f,g)$ the same criterion holds with $s=[d(f+g)-2]/(d-1)$ and $t=d(f-g)/(d-1)$. Restricting the Choi matrix to the four rank-$d$ partially transposed permutations gives exactly the filled ellipse $\lambda=d$. Every coordinatewise Pareto-optimal achievable pair belongs to that ellipse.
--
--   This gives both necessity and physical attainability, including negative shrink parameters.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 2, Theorem 1: introductory main result (original paper-result seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.2, Theorem 1, interpreted using pp.10,12–13: exact physical regions in
shrink and fidelity coordinates; every Pareto-optimal point lies on the lambda=d ellipse.
The filled lambda=d ellipse is the restricted feasible region, not all optimal points. -/
theorem main_cloning_region (d : ℕ) (hd : 2 ≤ d) (p q f g : ℝ) :
    (CloningAchievable d p q ↔ InEllipseUnion d (p + q) (p - q)) ∧
    (CloningFidelityAchievable d f g ↔
      InEllipseUnion d (((d : ℝ) * (f + g) - 2) / ((d : ℝ) - 1))
        ((d : ℝ) * (f - g) / ((d : ℝ) - 1))) ∧
    (RestrictedAchievable d p q ↔ InEllipse d (d : ℝ) (p + q) (p - q)) ∧
    (IsParetoOptimal d p q → InEllipse d (d : ℝ) (p + q) (p - q)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
