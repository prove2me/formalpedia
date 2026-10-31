-- Prove2me | Theorems.Thm_RiskExpPG_lemma_1
-- name    : RiskExpPG.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:19.240512+00:00
-- url     : https://prove2.me/theorems/39dea4c8-720e-4eb3-97ac-80f0f6f1b328
-- title:
--   Lemma 1 — uniform exponential moments of the return time over the closure of $\{P_\theta\}$
-- statement:
--   Suppose Assumption 1 holds. Then there is a constant $\overline R_{x^*}>1$ such that for any $R\in(1,\overline R_{x^*})$ there are $m(R),M(R)\in(1,\infty)$ with
--   $$m(R)<E^P_{\Phi_0=x}\big[R^{\tau_{x^*}}\big]<M(R)$$
--   for all $P\in\overline{\mathcal P}$ and $x\in\mathcal X$, and moreover $M(R)\downarrow1$ as $R\downarrow1$.
--
--   This uniform control of the return time gives bounds on all moments of $\tau_{x^*}$ that do not depend on $\theta$, on which all the estimates of the mission rest.
--
--   Differences from the source:
--   - encoding: irreducible and aperiodic → Matrix.IsPrimitive; reason: for a stochastic matrix on a finite type these are the same condition; no instance changes
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: M(R) ↓ 1 as R ↓ 1 → M is monotone on (1, R̄) and tends to 1 from the right; reason: this is the meaning of the arrow; no instance changes
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Lemma 1, p.22

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Lemma 1** (arXiv:2202.04157v2, p.22). Under Assumption 1, the return time to `x*` has
exponential moments uniformly over the closure of `{P_θ}` and over the initial state, and the
upper bound `M(R)` decreases to `1` as `R ↓ 1`. -/
theorem lemma_1 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) :
    UniformReturnMoments (closure (Set.range m.P)) m.xstar := by sorry

end RiskExpPG
