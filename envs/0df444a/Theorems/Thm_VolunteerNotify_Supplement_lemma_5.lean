-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_lemma_5
-- name    : VolunteerNotify.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:25:52.274381+00:00
-- url     : https://prove2.me/theorems/cd4df836-ee20-5925-8a5a-1034ada10bc5
-- title:
--   Lemma 5 — upper bound for instance $\mathcal I_2$
-- statement:
--   Let $n\ge1$, $q=1/n$, and let $\mathcal I_2$ be the instance with $V=n$ volunteers, one task type, $T=n^2+1$ periods, geometric inter-activity times with parameter $q$, arrival probabilities $\lambda_{1,1}=1$ and $\lambda_{1,t}=q$ for $t\ge2$, and match probabilities $p_{v,1}=q$. Then every online policy $\pi$ satisfies
--   $$
--   \mathrm{POL}_{\mathcal I_2}(\pi)\le\Big[1+q-\frac{q(1-q)}{\log\!\big(\frac1{1-q}\big)(1+q)}\big(1-e^{-1}\big)\Big]\mathrm{LP}_{\mathcal I_2}.
--   $$
--   This instance makes both the offline loss (between $f(x^*)$ and $\mathrm{LP}$) and the online loss large at the same time; it gives the second term of $\kappa$ in Theorem 2.
--
--   **Formalization Note** At $n=1$ the bracket is evaluated with Lean's conventions, which give $2$.
--
--   Differences from the source:
--   - reading: the bracket at q = 1 (n = 1), where log(1/(1−q)) = log(1/0) is undefined → `kappaTwo 1 = 2` by Lean's conventions (1/0 = 0, log 0 = 0, x/0 = 0); reason: 2 is the limit of the bracket as q → 1; the bound with 2 is the source's bound read at its boundary
--   - generalization: an online policy (§3, p.10): upon an arrival, an immediate irrevocable choice of whom to notify, knowing λ, p, g, without observing volunteers' states → `OnlinePolicy`: a randomized, non-anticipating behavioural rule that may also use the activity states up to t and the past responses; reason: the bound over the larger class implies the bound over the paper's class, which it contains; the proofs of Claim 4 (p.38) and fn. 24 (p.42) argue over this larger class; a mixed rule driven by a seed has a behavioural equivalent (finite horizon, perfect recall)
--   - encoding: POL_I, the expected number of completed tasks (Definition 3, p.12) → `polValue`: the `tsum` over the countable space of primitives and notified sets of their joint probability times `completedCount`; reason: the law of the process is discrete; the family is nonnegative and summable for every instance and policy, so the `tsum` is the expectation
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 5, p.22; Instance I2, p.22; proof in Appendix C.2, pp.37–42

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_Supplement_OnlinePolicy
import Definitions.Def_VolunteerNotify_Supplement_kappa
import Definitions.Def_VolunteerNotify_Supplement_instanceI2

namespace VolunteerNotify.Supplement

/-- Lemma 5, Manshadi–Rodilitz, arXiv:2002.08474v7, p.22: in instance `I2` with `q = 1/n`,
`n ∈ ℕ = {1, 2, …}`, the expected number of completed tasks under any online policy is at most
`[1 + q − q(1 − q)/(log(1/(1 − q))(1 + q)) (1 − e^{−1})] LP_{I2}`.

**Formalization Note.** At `n = 1` (`q = 1`) the printed bracket is undefined; Lean's conventions
give `kappaTwo 1 = 2` (see `kappaTwo`). -/
theorem lemma_5 (n : ℕ) (hn : 1 ≤ n) (π : OnlinePolicy (instanceI2 n hn)) :
    polValue (instanceI2 n hn) π ≤ kappaTwo (1 / (n : ℝ)) * lpValue (instanceI2 n hn) := by sorry

end VolunteerNotify.Supplement
