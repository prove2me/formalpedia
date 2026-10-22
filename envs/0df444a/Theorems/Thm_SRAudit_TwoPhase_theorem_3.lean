-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_theorem_3
-- name    : SRAudit.TwoPhase.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:41.009988+00:00
-- url     : https://prove2.me/theorems/7642fffb-bad7-447c-a919-2c7ca31537ac
-- title:
--   Theorem 3, p. 19 — an optimal auditing policy has two subphases
-- statement:
--   In the paper's three-tier supply network, let $\pi(g)$ be production profit, $a$ the audit cost, $r$ the rectification cost, $u$ the probability of noncompliance, $w$ the exposure probability, and $z$ the exposure penalty. Under the stated cost and probability assumptions, there is an admissible policy $\xi^*$ that maximizes the optimal action value at every state and has two subphases:
--
--   $$
--   ad\text{ actions first};\qquad
--   \begin{cases}
--     ar\text{ for every remaining supplier, in any order},&a+ur\leq uwz,\\
--     pp\text{ immediately},&a+ur\geq uwz.
--   \end{cases}
--   $$
--
--   In a rectification state, every available $ar(i)$ is optimal, and after any such choice the policy continues with an $ar$ action if unaudited suppliers remain. A $pp$ action with unaudited suppliers satisfies the second threshold. The first subphase may be empty, and both branches are permitted at equality.
--
--   **Formalization Note** These conditions hold at every state, including states that may not be reached from a given initial network. Production profit is universally quantified over functions of the network; this disclosed generalization follows §6.1 and the fact used in (D.27) that vetting does not change the production network.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 19 (PDF 19), Theorem 3

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase

theorem theorem_3 {ι : Type} [DecidableEq ι] (P : Params)
    (hP : P.Standing) (π : Network ι → ℝ) :
    ∃ ξ : Policy ι, IsOptimal P π ξ ∧
      (∀ (γ : State ι) (i : Supplier ι), ξ γ = .ar i →
        P.a + P.u * P.r ≤ P.u * P.w * P.z ∧
        (∀ j ∈ γ.U, Qstar P π γ (.ar j) = Vstar P π γ ∧
          ((vet γ j).U.Nonempty → ∃ k, ξ (vet γ j) = .ar k))) ∧
      (∀ γ : State ι, ξ γ = .pp → γ.U.Nonempty →
        P.u * P.w * P.z ≤ P.a + P.u * P.r) := by sorry

end SRAudit.TwoPhase
