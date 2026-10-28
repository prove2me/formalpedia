-- Prove2me | Theorems.Thm_RedundancyStab_IID_proposition_3
-- name    : RedundancyStab.IID.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:43.306122+00:00
-- url     : https://prove2.me/theorems/50dc2445-e278-4a4b-b2dd-f8c3cb82ab2f
-- title:
--   Proposition 3, p. 7 — under PS or ROS with i.i.d. copies, the redundancy-d system is stable (positive recurrent) when ρ = λ/(µK) < 1
-- statement:
--   Consider the redundancy-$d$ model with $K$ servers of capacity $1$, $1\le d\le K$: jobs arrive as a Poisson process of rate $\lambda>0$, each job sends copies to $d$ servers chosen uniformly at random, the copies have i.i.d. exponential service requirements of mean $1/\mu$ ($\mu>0$), and a job leaves, with all its copies removed, as soon as one copy completes. Let
--   $$\rho=\frac{\lambda}{\mu K}<1 .$$
--   Then the system is stable under each of the two service disciplines:
--
--   1. **Processor Sharing.** The continuous-time Markov chain $\vec N(t)=(N_c(t))_{c\in C}$ on $\mathbb N^{C}$ is positive recurrent: every state is recurrent and has finite mean return time.
--   2. **Random Order of Service.** The continuous-time Markov chain of the ROS configuration (job counts per type and per set of servers currently serving the job) is positive recurrent on the class of states reachable from the empty system: each such state is recurrent and has finite mean return time.
--
--   This is the paper's first main result: with i.i.d. copies, redundancy does not shrink the stability region $\rho<1$ under PS or ROS, which is the largest possible since the total service rate is at most $\mu K$.
--
--   **Formalization Note** Positive recurrence is the published `ProcessingNetworks.Stability.PositiveRecurrent` (recurrence of the jump chain and finite expected return time of the continuous-time chain, holding times $1/q$ included), applied to `psJump`/`psRate`. For ROS, `Recurrent` and `meanReturnTime < ⊤` are required for every state $x$ such that `0 < stepIter rosJump m rosEmpty x` for some $m$, i.e. on the communicating class of the empty state (states of the unconstrained count type that the system never visits are excluded); this is "the process started empty is positive recurrent". The only load hypothesis is $\lambda/(\mu K)<1$.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 7, Proposition 3 (stability defined on p. 5)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_RedundancyStab_IID_ROSChain

namespace RedundancyStab.IID

open ProcessingNetworks.Stability

theorem proposition_3 (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (hρ : lam / (μ * K) < 1) :
    PositiveRecurrent (psJump K d lam μ) (psRate K d lam μ) ∧
      ∀ x : RosState K d, (∃ m : ℕ, 0 < stepIter (rosJump K d lam μ) m (rosEmpty K d) x) →
        Recurrent (rosJump K d lam μ) x ∧
          meanReturnTime (rosJump K d lam μ) (rosRate K d lam μ) x < ⊤ := by sorry

end RedundancyStab.IID
