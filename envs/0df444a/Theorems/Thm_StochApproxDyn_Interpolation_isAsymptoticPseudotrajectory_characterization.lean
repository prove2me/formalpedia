-- Prove2me | Theorems.Thm_StochApproxDyn_Interpolation_isAsymptoticPseudotrajectory_characterization
-- name    : StochApproxDyn.Interpolation.isAsymptoticPseudotrajectory_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:09:09.30532+00:00
-- url     : https://prove2.me/theorems/96e8782e-96fb-4494-bda9-304adf626577
-- title:
--   Theorem 3.2 — characterization of precompact asymptotic pseudotrajectories of a flow
-- statement:
--   Let $\Phi$ be a flow on a metric space $M$ and let $X:\mathbb R_+\to M$ be a continuous function whose image has compact closure in $M$. Regard $X$ as an element of $C^0(\mathbb R,M)$ by $X(s)=X(0)$ for $s<0$, let $\Theta^t(X)(s)=X(t+s)$, and give $C^0(\mathbb R,M)$ the topology of uniform convergence on compact intervals. Consider:
--
--   1. $X$ is an asymptotic pseudotrajectory of $\Phi$;
--   2. $X$ is uniformly continuous, and every limit point $Y=\lim_k\Theta^{t_k}(X)$ with $t_k\to\infty$ lies in $S_\Phi=\{s\mapsto\Phi_s(p):p\in M\}$, i.e. is a fixed point of $\hat\Phi$;
--   3. $\{\Theta^t(X)\}_{t\ge0}$ is relatively compact in $C^0(\mathbb R,M)$.
--
--   Then (1) and (2) are equivalent, and they imply (3).
--
--   The theorem reduces the asymptotic pseudotrajectory property to two checks that can be made on the interpolated process directly: equicontinuity and identification of limit points as solutions. Proposition 4.1 under A2 is proved this way.
--
--   **Formalization Note** The paper states the theorem for a flow or a semiflow. It is stated here for a flow (`Flow ℝ M`); for a semiflow with the paper's convention $\Phi^p(t)=p$ for $t<0$, the implication (1) ⇒ (2) fails (a rotation of the circle, viewed as a semiflow, has itself as an asymptotic pseudotrajectory whose limit points are not constant at negative times). The flow of the vector field $F$ in the mission's goal is a flow.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 10–11, Theorem 3.2

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_AsymptoticPseudotrajectory

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Theorem 3.2, pp. 10–11, for a flow `Φ` on a metric space `M`, on `C⁰(ℝ, M)` with
the topology of uniform convergence on compact intervals (Mathlib's compact-open topology).
Let `X : ℝ₊ → M` be continuous with relatively compact image, extended to `ℝ` by `X(s) = X(0)`
for `s < 0`. Then (i) `X` is an asymptotic pseudotrajectory of `Φ` if and only if (ii) `X` is
uniformly continuous and every limit point `Y = lim_k Θ^{t_k}(X)`, `t_k → ∞`, lies in `S_Φ`
(is a fixed point of `Φ̂`); and (i) implies (iii) `{Θ^t(X)}_{t ≥ 0}` is relatively compact. -/
theorem isAsymptoticPseudotrajectory_characterization {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ M) (X : C(ℝ≥0, M)) (hX : IsCompact (closure (Set.range X))) :
    (IsAsymptoticPseudotrajectory Φ X ↔
      (UniformContinuous X ∧
        ∀ Y : C(ℝ, M), IsLimitPointOfTranslates X Y → Y ∈ trajectorySet Φ)) ∧
    (IsAsymptoticPseudotrajectory Φ X →
      IsCompact (closure (Set.range (translate X)))) := by sorry

end StochApproxDyn.Interpolation
