-- Prove2me | Theorems.Thm_RiskExpPG_corollary_4
-- name    : RiskExpPG.corollary_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:17.297124+00:00
-- url     : https://prove2.me/theorems/b2a3f1bd-6090-4172-b689-6bbbae984ac9
-- title:
--   Corollary 4 — Lemma 1 holds for the closure of the twisted kernels
-- statement:
--   Let Assumptions 1 and 2 hold, and let $\check{\mathcal P}=\{\check P_\theta:\theta\in\mathbb R^l\}$ be the set of twisted kernels
--   $$\check P_\theta(x,y)=\frac{\exp(\alpha C_\theta(x))\,P_\theta(x,y)\,h_\theta(y)}{\exp(\Lambda_\theta)\,h_\theta(x)}.$$
--   Then the conclusion of Lemma 1 holds for the closure of $\check{\mathcal P}$: there is $\overline R>1$ such that for any $R\in(1,\overline R)$ there are $m(R),M(R)\in(1,\infty)$ with $m(R)<\check E^{P}_{\Phi_0=x}[R^{\tau_{x^*}}]<M(R)$ for all $P$ in the closure and all $x$, and $M(R)\downarrow1$ as $R\downarrow1$.
--
--   The twisted expectation of $e^{(\Lambda_\theta-\Lambda)\tau_{x^*}}$ is $g(\theta,\Lambda)$, so this bound controls $g$ uniformly near $\Lambda_\theta$.
--
--   Differences from the source:
--   - encoding: irreducible and aperiodic → Matrix.IsPrimitive; reason: for a stochastic matrix on a finite type these are the same condition; no instance changes
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: h_θ the eigenvector of the multiplicative Poisson equation → h_θ given by the cycle expectation of Eq. (2) normalized as in Eq. (3); reason: Eq. (2)–(3) and Corollary 1 identify the two
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Corollary 4, p.23

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Corollary 4** (arXiv:2202.04157v2, p.23). Under Assumptions 1 and 2, the conclusion of Lemma 1
holds for the closure of the set `{P̌_θ}` of twisted kernels. -/
theorem corollary_4 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) :
    UniformReturnMoments (closure (Set.range m.twisted)) m.xstar := by sorry

end RiskExpPG
