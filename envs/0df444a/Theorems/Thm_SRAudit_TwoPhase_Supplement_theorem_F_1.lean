-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_F_1
-- name    : SRAudit.TwoPhase.Supplement.theorem_F_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:38:13.083867+00:00
-- url     : https://prove2.me/theorems/e9544218-71d0-4bba-b5aa-7317168981c3
-- title:
--   Theorem F.1, OA-31 — with tier-dependent penalties, some optimal policy audits and drops first, then rectifies the tiers k with a + ur ≤ uwz_k and proceeds to production
-- statement:
--   In the model of Appendix F (penalties $z_1,z_2$, standing parameters, any production profit $\pi$ of the network) there is an optimal policy $\xi^*$ whose decisions split into two subphases: an ad subphase (some suppliers, possibly none, are audited and dropped), followed by an rp subphase in which, writing $z_k$ for the penalty of supplier $k$'s tier,
--   1. if $a+ur\le uwz_1$ and $a+ur\le uwz_2$, all remaining unaudited suppliers are audited and rectified in any sequence, then pp;
--   2. if $a+ur\le uwz_1$ and $a+ur>uwz_2$, all remaining tier-1 suppliers are audited and rectified in any sequence, then pp;
--   3. if $a+ur>uwz_1$ and $a+ur\le uwz_2$, the same for tier 2;
--   4. if $a+ur>uwz_1$ and $a+ur>uwz_2$, pp directly.
--
--   Formally, at every state $\gamma$: if $\xi^*(\gamma)=\mathrm{ar}(i)$ then $a+ur\le uwz_i$, and for every unaudited $j$ with $a+ur\le uwz_j$, $\mathrm{ar}(j)$ is optimal at $\gamma$ and the policy at $\gamma\oplus j$ is again some $\mathrm{ar}$ while such a supplier remains unaudited, and $\mathrm{pp}$ otherwise; and if $\xi^*(\gamma)=\mathrm{pp}$ then every unaudited $j$ has $a+ur>uwz_j$. Along any path the ad actions therefore come first.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: 'auditing decisions are divided into two subphases' → a property of ξ* at every state: an ar is followed only by ar's of rectifiable suppliers and then pp, every rectifiable ar is optimal there, and pp leaves only non-rectifiable suppliers; reason: the same per-state rendering as the published Theorem 3 of this mission; it holds on every state, which implies the property along every path
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-31, Theorem F.1

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Heterogeneous

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_F_1 {ι : Type} [DecidableEq ι] (P : ParamsF) (hP : P.Standing)
    (π : Network ι → ℝ) :
    ∃ ξ : Policy ι, IsOptimalF P π ξ ∧
      -- an `ar` action belongs to the rp subphase: it rectifies a supplier of a tier `k` with
      -- `a + ur ≤ uwz_k`, every such supplier may be rectified next, and afterwards the policy
      -- keeps rectifying while such a supplier remains unaudited, then proceeds to production
      (∀ (γ : State ι) (i : Supplier ι), ξ γ = .ar i →
        P.a + P.u * P.r ≤ P.u * P.w * P.zOf i ∧
        ∀ j ∈ γ.U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf j →
          QstarF P π γ (.ar j) = VstarF P π γ ∧
          ((∃ k ∈ (vet γ j).U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf k) →
            ∃ k, ξ (vet γ j) = .ar k) ∧
          ((∀ k ∈ (vet γ j).U, P.u * P.w * P.zOf k < P.a + P.u * P.r) →
            ξ (vet γ j) = .pp)) ∧
      -- `pp` leaves unaudited only suppliers of tiers `k` with `a + ur > uwz_k`
      (∀ γ : State ι, ξ γ = .pp → ∀ j ∈ γ.U, P.u * P.w * P.zOf j < P.a + P.u * P.r) := by sorry

end SRAudit.TwoPhase.Supplement
