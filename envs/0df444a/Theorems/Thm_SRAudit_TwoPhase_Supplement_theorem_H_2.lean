-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_H_2
-- name    : SRAudit.TwoPhase.Supplement.theorem_H_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:44:46.169888+00:00
-- url     : https://prove2.me/theorems/4c0c2138-0a1b-4929-ae7a-498024a72340
-- title:
--   Theorem H.2, OA-54 — on general supply networks, under Assumptions D.1–D.2 (Definition H.1 symmetry) and independent unaudited suppliers, the LVUS policy (H.2) is optimal at every reachable state
-- statement:
--   On general directed supply networks (Appendix H), with standing parameters and a production profit $\pi$ of the network satisfying Assumption D.1 and Assumption D.2 (symmetry in the sense of Definition H.1), let $\gamma_0\in\Gamma$ be such that in every $\gamma\in R^+(\gamma_0)$ no unaudited supplier is a dependent of another. Then at every $\gamma\in R^+(\gamma_0)$ the policy
--   $$\xi^*(\gamma)=\begin{cases}\mathrm{ad}(i),&i\in U_\gamma,\ u\nabla(\gamma,i)+a<c_{rp},\ \nabla(\gamma,i)\le\nabla(\gamma,i')\ \forall i'\in U_\gamma\\ \mathrm{rp},&u\nabla(\gamma,i)+a\ge c_{rp}\ \forall i\in U_\gamma\end{cases}\qquad\text{(H.2)}$$
--   is optimal: $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$ in the first case and $\pi(\gamma)-c_{rp}|U_\gamma|=V^*(\gamma)$ in the second.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: R+(γ0) → ReachH γ0: reflexive-transitive closure of ⊕/⊖ transitions; reason: |U| strictly decreases, so every chain is realised by some policy
--   - reading: Assumptions D.1, D.2 for any γ ∈ Γ → for every state whose digraph lies in G; reason: Γ is the set of states over G
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-54, Theorem H.2, (H.2), Definition H.1

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_GeneralNetwork

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_H_2 {V : Type} [DecidableEq V] (c : V) (P : Params) (hP : P.Standing)
    (π : GNet V → ℝ) (hD1 : AssumptionD1H (c := c) π) (hD2 : AssumptionD2H (c := c) π)
    (γ₀ : HState V c) (hγ₀ : γ₀.WellFormed)
    (hindep : ∀ γ, ReachH γ₀ γ → ∀ i ∈ γ.U, ∀ i' ∈ γ.U, i ≠ i' →
      i ∉ γ.g.dependents c i' ∧ i' ∉ γ.g.dependents c i) :
    ∀ γ, ReachH γ₀ γ →
      (∀ i, IsLVUSH π γ i → P.u * nablaH π γ i + P.a < crp P →
        QstarH P π γ (.ad i) = VstarH P π γ) ∧
      ((∀ i ∈ γ.U, crp P ≤ P.u * nablaH π γ i + P.a) → rpValueH P π γ = VstarH P π γ) := by sorry

end SRAudit.TwoPhase.Supplement
