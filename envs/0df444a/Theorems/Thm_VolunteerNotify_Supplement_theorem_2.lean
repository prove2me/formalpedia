-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_theorem_2
-- name    : VolunteerNotify.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:27:31.911749+00:00
-- url     : https://prove2.me/theorems/47a35e54-890d-41eb-938b-aacb4a51aceb
-- title:
--   Theorem 2 — no online policy is better than $\kappa(q)$-competitive
-- statement:
--   Let $q\in[1/16,1]\cup\{1/n:n\in\mathbb N\}\cup\{0\}$, where $\mathbb N=\{1,2,\dots\}$. Let $\pi$ be an online policy (one rule for every instance) and $c$ a real number such that $\pi$ is $c$-competitive on the instances whose inter-activity time distribution has MDHR $q$, that is,
--   $$
--   \mathrm{POL}_{\mathcal I}(\pi)\ge c\,\mathrm{LP}_{\mathcal I}\quad\text{for every such instance }\mathcal I .
--   $$
--   Then $c\le\kappa(q)$, where
--   $$
--   \kappa(q)=\min\Big\{\frac1{2-q},\ 1+q-\frac{q(1-q)}{\log\!\big(\frac1{1-q}\big)(1+q)}\big(1-e^{-1}\big)\Big\}\quad(q>0),\qquad\kappa(0)=0.334 .
--   $$
--   This is the paper's impossibility result. It holds for all online policies, including those that cannot be computed in polynomial time, and it shows that the SN policy of Theorem 1 is close to optimal when $q$ is small.
--
--   **Formalization Note** "The MDHR is $q$" means that the minimum of the hazard rates exists and equals $q$, as in Definition 1. At $q=1$, $\kappa(1)=1$ by Lean's conventions, the value of footnote 21.
--
--   Differences from the source:
--   - generalization: an online policy (§3, p.10): upon an arrival, an immediate irrevocable choice of whom to notify, knowing λ, p, g, without observing volunteers' states → `OnlinePolicy`: a randomized, non-anticipating behavioural rule that may also use the activity states up to t and the past responses; reason: the bound over the larger class implies the bound over the paper's class, which it contains; the proofs of Claim 4 (p.38) and fn. 24 (p.42) argue over this larger class; a mixed rule driven by a seed has a behavioural equivalent (finite horizon, perfect recall)
--   - reading: "Suppose the MDHR is q … no online policy can achieve a competitive ratio greater than κ" with Definition 3's "for any instance" → for every policy family π and real c with c·LP_I ≤ POL_I(π) for every instance I whose hazard minimum is q, c ≤ κ(q); reason: the ratio is parameterized by q, as for Theorem 1; the proof uses instances with MDHR q
--   - reading: κ at q = 1 from (18), where log(1/(1−q)) is undefined → Lean's conventions give the second term 2, so κ(1) = 1; reason: fn. 21: for q = 1 no online policy can achieve a ratio greater than 1
--   - encoding: POL_I, the expected number of completed tasks (Definition 3, p.12) → `polValue`: the `tsum` over the countable space of primitives and notified sets of their joint probability times `completedCount`; reason: the law of the process is discrete; the family is nonnegative and summable for every instance and policy, so the `tsum` is the expectation
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Theorem 2 and (18), p.21; fn. 20–21, p.21; Definition 3, p.12

import Mathlib
import Definitions.Def_VolunteerNotify_mdhr
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_Supplement_OnlinePolicy
import Definitions.Def_VolunteerNotify_Supplement_kappa

namespace VolunteerNotify.Supplement

/-- Theorem 2, Manshadi–Rodilitz, arXiv:2002.08474v7, p.21: suppose the MDHR of the inter-activity
time distribution is `q ∈ [1/16, 1] ∪ {1/n : n ∈ ℕ} ∪ {0}`. Then no online policy can achieve a
competitive ratio greater than `κ(q)` of (18) (`κ = 0.334` at `q = 0`). Here `π` is an online
policy, one rule for each instance, and "`π` is `c`-competitive" (Definition 3, p.12) is
`c · LP_I ≤ POL_I` for every instance `I` whose distribution has MDHR `q`.

**Formalization Note.** "The MDHR is `q`" is read as in Definition 1, p.10: the minimum of the
hazard rates over `τ ∈ ℕ` exists and equals `q` (`IsLeast` of the range of `hazard I.g (τ + 1)`).
This is the source's class of instances; the infimum `mdhr` would admit more instances into the
hypothesis and weaken the theorem. `ℕ = {1, 2, …}`. The policy class is `OnlinePolicy` (randomized,
non-anticipating, may observe states and responses), which contains the paper's; `POL_I` is
`polValue`, defined for every instance and policy. -/
theorem theorem_2 (q : ℝ)
    (hq : q ∈ Set.Icc (1 / 16 : ℝ) 1 ∨ (∃ n : ℕ, 1 ≤ n ∧ q = 1 / (n : ℝ)) ∨ q = 0)
    (π : ∀ {V S T : ℕ} (I : Instance V S T), OnlinePolicy I) (c : ℝ)
    (hc : ∀ (V S T : ℕ) (I : Instance V S T),
      IsLeast (Set.range fun τ : ℕ => hazard I.g (τ + 1)) q → c * lpValue I ≤ polValue I (π I)) :
    c ≤ kappa q := by sorry

end VolunteerNotify.Supplement
