-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_H_1
-- name    : SRAudit.TwoPhase.Supplement.theorem_H_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:44:11.093383+00:00
-- url     : https://prove2.me/theorems/86c3e3fd-465a-4393-b100-5ea503a5930b
-- title:
--   Theorem H.1, OA-54 — on general supply networks, some optimal policy audits and drops first, then rectifies all or proceeds to production
-- statement:
--   On general directed supply networks (Appendix H: a finite digraph with buyer $c$, path-based dependents, $\gamma\ominus i$ the induced subgraph without $D_g(i)$), with standing parameters and any production profit $\pi$ of the network, there is an optimal policy $\xi^*$ whose decisions split into an ad subphase (audit and drop some suppliers, possibly none) followed by an rp subphase that audits and rectifies all remaining unaudited suppliers in an arbitrary sequence if $a+ur\le uwz$, or proceeds to production if $a+ur\ge uwz$.
--
--   Formally, at every state $\gamma$: if $\xi^*(\gamma)=\mathrm{ar}(i)$ then $a+ur\le uwz$, every $\mathrm{ar}(j)$, $j\in U_\gamma$, is optimal at $\gamma$, and the policy at $\gamma\oplus j$ is again an $\mathrm{ar}$ whenever $\gamma\oplus j$ is nonterminal; and if $\xi^*(\gamma)=\mathrm{pp}$ with $U_\gamma\ne\emptyset$ then $uwz\le a+ur$.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - generalization: states (g, U) with g ∈ G → states over every finite digraph; reason: the proof of Theorem 3 uses only ⊕, ⊖ and the dependents relation, which are defined on any digraph; G is closed under ⊖, so an optimal policy on all states restricts to one on Γ
--   - reading: 'auditing decisions are divided into two subphases' → the per-state property of the published Theorem 3; reason: holds at every state, hence along every path
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-54, Theorem H.1 (model OA-53–OA-54)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_GeneralNetwork

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_H_1 {V : Type} [DecidableEq V] (c : V) (P : Params) (hP : P.Standing)
    (π : GNet V → ℝ) :
    ∃ ξ : HPolicy V c, IsOptimalH P π ξ ∧
      (∀ (γ : HState V c) (i : V), ξ γ = .ar i →
        P.a + P.u * P.r ≤ P.u * P.w * P.z ∧
        (∀ j ∈ γ.U, QstarH P π γ (.ar j) = VstarH P π γ ∧
          ((γ.vet j).U.Nonempty → ∃ k, ξ (γ.vet j) = .ar k))) ∧
      (∀ γ : HState V c, ξ γ = .pp → γ.U.Nonempty →
        P.u * P.w * P.z ≤ P.a + P.u * P.r) := by sorry

end SRAudit.TwoPhase.Supplement
