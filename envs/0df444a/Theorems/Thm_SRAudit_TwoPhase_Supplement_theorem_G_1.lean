-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_G_1
-- name    : SRAudit.TwoPhase.Supplement.theorem_G_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:40:09.636914+00:00
-- url     : https://prove2.me/theorems/fbd23ebd-0d3b-44c9-b697-54ca47aaf456
-- title:
--   Theorem G.1, OA-40 — with inaccurate audits, some optimal policy audits and drops first, then rectifies all if a + udr < wz(u − û) or produces if a + udr ≥ wz(u − û)
-- statement:
--   In the inaccurate-audit model of Appendix G with $C=\emptyset$ (standing parameters, $d\in[0,1]$, any production profit $\pi$ of the network) there is an optimal policy $\xi^*$ whose decisions split into an ad subphase (audit and drop some suppliers, possibly none) followed by an rp subphase that audits and rectifies all remaining unaudited suppliers in an arbitrary sequence if $a+udr<wz(u-\hat u)$, or proceeds to production if $a+udr\ge wz(u-\hat u)$.
--
--   Formally, at every state $\gamma$: if $\xi^*(\gamma)=\mathrm{ar}(i)$ then $a+udr<wz(u-\hat u)$, every $\mathrm{ar}(j)$, $j\in U_\gamma$, is optimal at $\gamma$, and the policy at $\gamma\oplus j$ is again an $\mathrm{ar}$ whenever $\gamma\oplus j$ is nonterminal; and if $\xi^*(\gamma)=\mathrm{pp}$ with $U_\gamma\ne\emptyset$ then $a+udr\ge wz(u-\hat u)$.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: 'auditing decisions are divided into two subphases' → the per-state property of the published Theorem 3, with the thresholds of Theorem G.1 (strict for ar, weak for pp); reason: holds at every state, hence along every path
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-40, Theorem G.1

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_G_1 {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (π : Network ι → ℝ) :
    ∃ ξ : Policy ι, IsOptimalG P d ∅ π ξ ∧
      (∀ (γ : State ι) (i : Supplier ι), ξ γ = .ar i →
        P.a + P.u * d * P.r < P.w * P.z * (P.u - uhat P d) ∧
        (∀ j ∈ γ.U, QstarG P d ∅ π γ (.ar j) = VstarG P d ∅ π γ ∧
          ((vet γ j).U.Nonempty → ∃ k, ξ (vet γ j) = .ar k))) ∧
      (∀ γ : State ι, ξ γ = .pp → γ.U.Nonempty →
        P.w * P.z * (P.u - uhat P d) ≤ P.a + P.u * d * P.r) := by sorry

end SRAudit.TwoPhase.Supplement
