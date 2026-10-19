-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_proposition_D_1
-- name    : SRAudit.TwoPhase.proposition_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:39.892968+00:00
-- url     : https://prove2.me/theorems/15adf77a-22ab-4ac2-a87c-bb876ea8e979
-- title:
--   Proposition D.1, OA-11 — postponing rectification until after dropping
-- statement:
--   Let $\xi$ be an admissible auditing policy on the three-tier supply network, with nonnegative audit and rectification costs, noncompliance probability $u\in(0,1)$, exposure probability $w\in(0,1]$, and nonnegative exposure penalty. For each starting state $\gamma$, there is an admissible policy $\xi'$ whose audit-and-rectify actions are never followed by audit-and-drop actions and whose value is no smaller at that state:
--
--   $$
--   \forall\gamma\;\exists\xi',\quad V(\xi,\gamma)\leq V(\xi',\gamma).
--   $$
--
--   This is the ordering result used to obtain a policy with a dropping subphase before its rectification subphase.
--
--   **Formalization Note** The value comparison is at each chosen starting state, as in the appendix's swap argument; the policy chosen may depend on that state. The replacement policy is ordered on all states. Production profit is any real-valued function of the current network; this extends the paper's Cournot production model as discussed in §6.1.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-11 (PDF 46), Proposition D.1

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase

theorem proposition_D_1 {ι : Type} [DecidableEq ι] (P : Params)
    (hP : P.Standing) (π : Network ι → ℝ) (ξ : Policy ι)
    (hξ : IsAdmissible ξ) :
    ∀ γ : State ι, ∃ ξ' : Policy ι, IsAdmissible ξ' ∧
      (∀ (γ' : State ι) (i j : Supplier ι),
        ξ' γ' = .ar i → ξ' (vet γ' i) ≠ .ad j) ∧
      Vpol P π ξ γ ≤ Vpol P π ξ' γ := by sorry

end SRAudit.TwoPhase
