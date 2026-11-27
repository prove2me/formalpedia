-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_G_1
-- name    : SRAudit.TwoPhase.Supplement.proposition_G_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:38:50.478796+00:00
-- url     : https://prove2.me/theorems/0e8e2b04-ad83-49ef-97d5-77264e163c2e
-- title:
--   Proposition G.1, OA-37 — with inaccurate audits, postponing every ar action until after every ad action never lowers the buyer's value
-- statement:
--   In the inaccurate-audit model of Appendix G with $C=\emptyset$ (detection probability $d\in[0,1]$, standing parameters, any production profit $\pi$ of the network), let $\xi$ be an admissible policy and $\gamma$ a state. Then there is an admissible policy $\xi'$ in which no $\mathrm{ad}$ action immediately follows an $\mathrm{ar}$ action anywhere ($\xi'(\gamma')=\mathrm{ar}(i)$ implies $\xi'(\gamma'\oplus i)\ne\mathrm{ad}(j)$ for all $\gamma',i,j$), and
--   $$V(\xi,\gamma)\le V(\xi',\gamma),$$
--   where $V$ is the policy value of (D.1), (G.3)–(G.5). This is the first half of the proof of Theorem G.1.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: 'the buyer can be at least as well off by postponing all ar actions to after all ad actions' → for every admissible ξ and state γ there is an admissible ξ′ with no ad right after an ar and V(ξ,γ) ≤ V(ξ′,γ); reason: the same rendering as the published Proposition D.1 of this mission, in the Appendix G model
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-37, Proposition G.1, (G.3)–(G.5)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_G_1 {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (π : Network ι → ℝ) (ξ : Policy ι) (hξ : IsAdmissible ξ) :
    ∀ γ : State ι, ∃ ξ' : Policy ι, IsAdmissible ξ' ∧
      (∀ (γ' : State ι) (i j : Supplier ι), ξ' γ' = .ar i → ξ' (vet γ' i) ≠ .ad j) ∧
      VpolG P d ∅ π ξ γ ≤ VpolG P d ∅ π ξ' γ := by sorry

end SRAudit.TwoPhase.Supplement
