-- Prove2me | Theorems.Thm_RiskBalancingMNL_Supplement_zeta_unique_root
-- name    : RiskBalancingMNL.Supplement.zeta_unique_root
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:59:07.925796+00:00
-- url     : https://prove2.me/theorems/3b6d3c45-9109-4e19-a5c3-f33aedba33f4
-- title:
--   Claim, p.18 — $\zeta$ decreases from $(\pi/\lambda)^2$ to $-\infty$ and has a unique root $\theta(\pi)\ge0$
-- statement:
--   Consider the MNL model with asymmetric price sensitivities $\hat b_i>0$, a risk weight $\lambda\in(0,1)$ and any real $\pi$. Let
--   $$
--   \zeta(\theta)=\Big(\frac\pi\lambda\Big)^2+2\sum_{i=1}^n\frac{e^{\hat a_i-\hat b_ic_i-1}}{\hat b_i}\Big(\frac1{\hat b_i}-\sqrt{\big(\tfrac1{\hat b_i}\big)^2+\theta}\Big)\exp\Big(-\hat b_i\Big(\frac\pi\lambda-\sqrt{\big(\tfrac1{\hat b_i}\big)^2+\theta}\Big)\Big)-\theta .
--   $$
--   Then:
--   1. $\zeta$ is strictly decreasing on $[0,\infty)$;
--   2. $\zeta(\theta)\to(\pi/\lambda)^2$ as $\theta\to0^+$;
--   3. $\zeta(\theta)\to-\infty$ as $\theta\to\infty$;
--   4. $\zeta$ has exactly one root in $[0,\infty)$;
--   5. that root is $\theta(\pi)$: $\theta(\pi)\ge0$ and $\zeta(\theta(\pi))=0$.
--
--   The root $\theta(\pi)$ defines the markups $m_j(\pi,\theta(\pi))$ and the fixed-point map $f$ of (27), which reduce the $n$-dimensional asymmetric problem to a search over the profit level $\pi$.
--
--   Differences from the source:
--   - reading: λ (the risk weight of §5.2) → 0 < λ < 1; reason: ζ contains π/λ, undefined at λ = 0
--   - reading: ζ(θ) monotonically decreases in θ → ζ strictly decreasing on [0, ∞); reason: the uniqueness conclusion needs strict decrease; the domain of θ is [0, ∞) (θ ≥ 0 by Lemma 5)
--   - reading: lim_{θ→0} ζ(θ) = (π/λ)² → one-sided limit as θ → 0⁺; reason: θ ranges over [0, ∞)
--   - reading: a unique θ with ζ(θ) = 0 for any π → exactly one θ ≥ 0 with ζ(θ) = 0, for every real π; reason: the root lies in the domain [0, ∞); every real π is allowed
--   - encoding: θ(π) denotes that root → the defined θ(π) (thetaOf) is ≥ 0 and a root of ζ; reason: ties the definition of θ(π) to the claim
--   - encoding: primitives a_i, y_i, b, β of (16) → reduced form â_i, b̂_i > 0, c_i; reason: the primitives enter only through â_i = a_i + y_i and b̂_i = b − βy_i, and every positive b̂ arises
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5.2, the definition of $\zeta$ and the sentence following it, p.18

import Mathlib
import Definitions.Def_RiskBalancingMNL_Supplement_zeta

open Filter Topology

namespace RiskBalancingMNL.Supplement

/-- **The unique root `θ(π)` of `ζ`**, Li & Webster, *Optimizing Risk-balancing Return under
Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), §5.2, p.18: "given `π`, `ζ(θ)`
monotonically decreases in `θ` and … `lim_{θ→0} ζ(θ) = (π/λ)²` and `lim_{θ→∞} ζ(θ) = −∞`. Hence
there exists a unique `θ` that satisfies `ζ(θ) = 0` for any `π`, which we denote with `θ(π)`."

For `λ ∈ (0, 1)` and every real `π`:
1. `ζ` is strictly decreasing on `[0, ∞)`;
2. `ζ(θ) → (π/λ)²` as `θ → 0⁺`;
3. `ζ(θ) → −∞` as `θ → ∞`;
4. `ζ` has exactly one root in `[0, ∞)`;
5. that root is `θ(π)` (`thetaOf`): `θ(π) ≥ 0` and `ζ(θ(π)) = 0`.

**Formalization Note** "Monotonically decreases" is read as strictly decreasing, which the
uniqueness conclusion needs. The domain of `θ` is `[0, ∞)`, the range of `θ` by Lemma 5. -/
theorem zeta_unique_root {n : ℕ} (P : AsymParams n) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : ℝ) :
    StrictAntiOn (zeta P lam π) (Set.Ici 0) ∧
    Tendsto (zeta P lam π) (𝓝[>] 0) (𝓝 ((π / lam) ^ 2)) ∧
    Tendsto (zeta P lam π) atTop atBot ∧
    (∃! θ : ℝ, 0 ≤ θ ∧ zeta P lam π θ = 0) ∧
    (0 ≤ thetaOf P lam π ∧ zeta P lam π (thetaOf P lam π) = 0) := by sorry

end RiskBalancingMNL.Supplement
