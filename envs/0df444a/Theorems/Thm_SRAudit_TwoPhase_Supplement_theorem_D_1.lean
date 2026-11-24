-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_D_1
-- name    : SRAudit.TwoPhase.Supplement.theorem_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:36:02.450678+00:00
-- url     : https://prove2.me/theorems/3a9150d2-7a37-4075-a621-7a5483beb710
-- title:
--   Theorem D.1, OA-14 — under Assumptions D.1–D.2 and independent unaudited suppliers, the LVUS policy (D.36) is optimal at every reachable state
-- statement:
--   Let the parameters satisfy the standing assumptions and let $\pi$ be any production profit (a function of the network) satisfying Assumptions D.1 and D.2. Let $\gamma_0\in\Gamma$ be such that in every state $\gamma\in R^+(\gamma_0)$ no unaudited supplier is a dependent of another: $i\notin D_g(i')$ and $i'\notin D_g(i)$ for distinct $i,i'\in U_\gamma$. Then at every $\gamma\in R^+(\gamma_0)$ the policy
--   $$\xi^*(\gamma)=\begin{cases}\mathrm{ad}(i),&i\in U_\gamma,\ u\nabla(\gamma,i)+a<c_{rp},\ \nabla(\gamma,i)\le\nabla(\gamma,i')\ \forall i'\in U_\gamma\\ \mathrm{rp},&u\nabla(\gamma,i)+a\ge c_{rp}\ \forall i\in U_\gamma\end{cases}\qquad\text{(D.36)}$$
--   is optimal: in the first case $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$, in the second $\pi(\gamma)-c_{rp}|U_\gamma|=V^*(\gamma)$.
--
--   Its proof is the template for Theorems D.2, G.3 and H.2.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: R+(γ0): states reached with positive probability under some policy → Reach γ0: reflexive-transitive closure of γ ↦ γ⊕i, γ⊖i (i ∈ U_γ); reason: |U| strictly decreases along transitions, so every chain is realised by a stationary policy, and u ∈ (0,1) gives both outcomes of ad positive probability
--   - reading: Assumptions D.1, D.2 for any γ ∈ Γ → for every well-formed state; reason: Γ is the set of states over G
--   - reading: Definition D.1 lists the pairs (i ∈ S_a, i′ ∈ S_b) and (i = a, i′ = b) → both orders of each pair; reason: 'two suppliers are symmetric' is a symmetric relation; Assumption D.2 uses 'i′ and i are not symmetric'
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-14, Theorem D.1, (D.34)–(D.36); R+ on OA-11

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_D_1 {ι : Type} [DecidableEq ι] (P : Params) (hP : P.Standing)
    (π : Network ι → ℝ) (hD1 : AssumptionD1 π) (hD2 : AssumptionD2 π)
    (γ₀ : State ι) (hγ₀ : WellFormedState γ₀)
    (hindep : ∀ γ, Reach γ₀ γ → ∀ i ∈ γ.U, ∀ i' ∈ γ.U, i ≠ i' →
      i ∉ γ.g.dependents i' ∧ i' ∉ γ.g.dependents i) :
    ∀ γ, Reach γ₀ γ →
      (∀ i, IsLVUS π γ i → P.u * nabla π γ i + P.a < crp P →
        Qstar P π γ (.ad i) = Vstar P π γ) ∧
      ((∀ i ∈ γ.U, crp P ≤ P.u * nabla π γ i + P.a) → rpValue P π γ = Vstar P π γ) := by sorry

end SRAudit.TwoPhase.Supplement
