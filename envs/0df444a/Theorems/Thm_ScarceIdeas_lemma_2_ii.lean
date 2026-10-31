-- Prove2me | Theorems.Thm_ScarceIdeas_lemma_2_ii
-- name    : ScarceIdeas.lemma_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:05.820776+00:00
-- url     : https://prove2.me/theorems/805a344f-b625-4fc8-8ec6-e311995ad46e
-- title:
--   Lemma 2 (ii): $m_k(\phi)=k!/\phi^k+o(1/\phi^k)$
-- statement:
--   Let $h_0$ satisfy Assumption 1 and let $k\ge1$. Then
--
--   $$\lim_{\phi\to\infty}\phi^k\,m_k(\phi)=k!\qquad\text{and}\qquad\lim_{\phi\to\infty}m_k(\phi)=0 .$$
--
--   As the planner's incentive grows without an innovation, her beliefs concentrate at $\lambda=0$ at a rate fixed by $h_0(0)>0$ alone.
--
--   Differences from the source:
--
--   - encoding: m_k(ϕ) = k!/ϕ^k + o(1/ϕ^k) → ϕ^k m_k(ϕ) → k! as ϕ → ∞; reason: equivalent by the definition of o(·)
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, Lemma 2 (ii), p.20; proof p.35, (34)

import Mathlib
import Definitions.Def_ScarceIdeas_Assumption1
import Definitions.Def_ScarceIdeas_moment

namespace ScarceIdeas

open Filter Topology

/-- **Lemma 2 (ii): `m_k(ϕ) = k!/ϕ^k + o(1/ϕ^k)` as `ϕ → ∞`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
Lemma 2 (ii), p.20; proof p.35, (34).

Under Assumption 1, for every `k ≥ 1`,

$$\lim_{\phi\to\infty}\phi^k\,m_k(\phi)=k!\qquad\text{and}\qquad \lim_{\phi\to\infty}m_k(\phi)=0 .$$

**Formalization Note** `m_k(ϕ) = k!/ϕ^k + o(1/ϕ^k)` is stated in the equivalent form
`ϕ^k m_k(ϕ) → k!`. -/
theorem lemma_2_ii (h0 : ℝ → ℝ) (h0A : Assumption1 h0) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun ϕ : ℝ => ϕ ^ k * moment h0 k ϕ) atTop (𝓝 (k.factorial : ℝ)) ∧
    Tendsto (moment h0 k) atTop (𝓝 0) := by sorry

end ScarceIdeas
