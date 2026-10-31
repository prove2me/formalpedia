-- Prove2me | Theorems.Thm_ScarceIdeas_lemma_2_i
-- name    : ScarceIdeas.lemma_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:09.227987+00:00
-- url     : https://prove2.me/theorems/125e4c8d-d950-4a8f-bf04-a1703a425c14
-- title:
--   Lemma 2 (i): the moments are positive, $C^1$, strictly decreasing, with $m_k'=m_km_1-m_{k+1}<0$
-- statement:
--   Let $h_0$ satisfy Assumption 1 and let $k\ge1$. For every state $\phi\ge0$, the integral $\int_0^\infty\lambda^kh_0(\lambda)e^{-\lambda\phi}d\lambda$ is finite, the normalizer $Z(\phi)$ is positive, and $m_k(\phi)>0$. Moreover $m_k$ is continuously differentiable on $[0,\infty)$ with
--
--   $$\frac{dm_k(\phi)}{d\phi}=m_k(\phi)m_1(\phi)-m_{k+1}(\phi)<0 ,$$
--
--   and $m_k$ is strictly decreasing on $[0,\infty)$. For $k=1$ this is (15): $m_1'=m_1^2-m_2=-\mathrm{Var}_\phi(\lambda)<0$.
--
--   The equations of motion of the moments do not depend on the reward policy; they are the input to the policy dynamics (24).
--
--   Differences from the source:
--
--   - encoding: all ϕ; dV/dϕ, dp/dϕ → ϕ ≥ 0, derivatives within [0, ∞); reason: the state ϕ = ∫F ≥ 0 lives in ℝ₊ (the space S, p.36); one-sided derivatives at the boundary state 0
--   - encoding: −Cov_ϕ(λ, λ^k) in (14), −Var_ϕ(λ) in (15) → the equal expression m_k m_1 − m_{k+1}, and its k = 1 case; reason: the posterior covariance is m_{k+1} − m_k m_1 by definition; (15) is (14) at k = 1
--   - encoding: the moments are finite → λ^k h0(λ) e^{−λϕ} is integrable on (0, ∞) and Z(ϕ) > 0; reason: m_k is the quotient (31), finite exactly when its numerator is integrable and its denominator positive
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Lemma 2 (i), pp.19–20, (14)–(15); proof p.34, (31)–(33)

import Mathlib
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_moment

namespace ScarceIdeas

/-- **Lemma 2 (i) [Evolution of the moments]: finiteness, positivity, and the equations of motion
(14)–(15).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Lemma 2 (i), pp.19–20, (14)–(15); proof pp.34 ((31)–(33)).

Under Assumption 1, for every `k ≥ 1`: the moment integral is finite and the normalizer is
positive at every state `ϕ ≥ 0`; `m_k(ϕ) > 0`; `m_k` is continuously differentiable on `[0, ∞)`
with

$$\frac{dm_k(\phi)}{d\phi}=m_k(\phi)m_1(\phi)-m_{k+1}(\phi)<0 ,$$

and `m_k` is strictly decreasing on `[0, ∞)`. (15) is the case `k = 1`.

**Formalization Note** States are `ϕ ≥ 0`; derivatives are taken within `[0, ∞)` (one-sided at
`0`). The middle expression `−Cov_ϕ(λ, λ^k)` of (14) is the same number `m_k m_1 − m_{k+1}` and
is not restated. -/
theorem lemma_2_i (h0 : ℝ → ℝ) (h0A : Assumption1 h0) (k : ℕ) (hk : 1 ≤ k) :
    (∀ ϕ : ℝ, 0 ≤ ϕ →
        MeasureTheory.IntegrableOn (fun lam => lam ^ k * h0 lam * Real.exp (-lam * ϕ))
          (Set.Ioi 0) ∧
        0 < normalizer h0 ϕ ∧ 0 < moment h0 k ϕ) ∧
    ContDiffOn ℝ 1 (moment h0 k) (Set.Ici 0) ∧
    (∀ ϕ : ℝ, 0 ≤ ϕ →
        HasDerivWithinAt (moment h0 k) (moment h0 k ϕ * moment h0 1 ϕ - moment h0 (k + 1) ϕ)
          (Set.Ici 0) ϕ) ∧
    (∀ ϕ : ℝ, 0 ≤ ϕ → moment h0 k ϕ * moment h0 1 ϕ - moment h0 (k + 1) ϕ < 0) ∧
    StrictAntiOn (moment h0 k) (Set.Ici 0) := by sorry

end ScarceIdeas
