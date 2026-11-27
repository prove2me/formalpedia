-- Prove2me | Theorems.Thm_VolunteerNotify_Supplement_lemma_6
-- name    : VolunteerNotify.Supplement.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:26:50.294397+00:00
-- url     : https://prove2.me/theorems/bb2d6057-1a03-4e30-8d7d-aad9eff7881b
-- title:
--   Lemma 6 — upper bound $0.334$ for instance $\mathcal I_3$
-- statement:
--   For $n\ge1$ let $\mathcal I_3(n)$ be the instance with $V=n$ volunteers, one task type, $T=n^2$ periods, deterministic inter-activity time of length $n$, arrival probabilities $\lambda_{1,t}=1/n$ and match probabilities $p_{v,1}=1/n$. There is $N$ such that for every $n\ge N$ and every online policy $\pi$,
--   $$
--   \mathrm{POL}_{\mathcal I_3(n)}(\pi)\le 0.334\cdot\mathrm{LP}_{\mathcal I_3(n)} .
--   $$
--   The MDHR of this instance is $0$, and the lemma gives the value $\kappa(0)=0.334$ in Theorem 2.
--
--   **Formalization Note** The source defines $\mathcal I_3$ with "$V=n$ for sufficiently large $n$"; this is the quantifier $\exists N\,\forall n\ge N$. For $n=1$ the bound is false ($\mathrm{POL}=\mathrm{LP}=1$).
--
--   Differences from the source:
--   - reading: Instance I3 with "V = n for sufficiently large n" (p.23) → ∃ N, ∀ n ≥ N; reason: the source's qualifier; the bound fails at n = 1, so it cannot hold for every n
--   - generalization: an online policy (§3, p.10): upon an arrival, an immediate irrevocable choice of whom to notify, knowing λ, p, g, without observing volunteers' states → `OnlinePolicy`: a randomized, non-anticipating behavioural rule that may also use the activity states up to t and the past responses; reason: the bound over the larger class implies the bound over the paper's class, which it contains; the proofs of Claim 4 (p.38) and fn. 24 (p.42) argue over this larger class; a mixed rule driven by a seed has a behavioural equivalent (finite horizon, perfect recall)
--   - encoding: POL_I, the expected number of completed tasks (Definition 3, p.12) → `polValue`: the `tsum` over the countable space of primitives and notified sets of their joint probability times `completedCount`; reason: the law of the process is discrete; the family is nonnegative and summable for every instance and policy, so the `tsum` is the expectation
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1; reason: Lean convention; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Lemma 6, p.23; Instance I3, p.23; proof in Appendix C.3, pp.42–44

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_Supplement_OnlinePolicy
import Definitions.Def_VolunteerNotify_Supplement_instanceI3

namespace VolunteerNotify.Supplement

/-- Lemma 6, Manshadi–Rodilitz, arXiv:2002.08474v7, p.23: in instance `I3` (`V = n` "for
sufficiently large `n`", p.23), the expected number of completed tasks under any online policy is
at most `0.334 × LP_{I3}`.

**Formalization Note.** "Sufficiently large" is `∃ N, ∀ n ≥ N`. The bound fails at `n = 1`
(one volunteer, one period, `λ = p = 1`: `POL = LP = 1`), so the qualifier is part of
the statement. `0.334` is the exact decimal `334/1000`. -/
theorem lemma_6 :
    ∃ N : ℕ, ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → ∀ π : OnlinePolicy (instanceI3 n hn),
      polValue (instanceI3 n hn) π ≤ 334 / 1000 * lpValue (instanceI3 n hn) := by sorry

end VolunteerNotify.Supplement
