-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_G_3
-- name    : SRAudit.TwoPhase.Supplement.theorem_G_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:42:09.813319+00:00
-- url     : https://prove2.me/theorems/a0416891-78b8-4c28-aa8d-6c391107ec28
-- title:
--   Theorem G.3, OA-41 — inaccurate audits, Assumptions D.1–D.2, perfectly compliant vetted dependents: the LVUS policy (G.46) is optimal at every reachable state
-- statement:
--   In the inaccurate-audit model of Appendix G with a set $C$ of suppliers that are perfectly compliant once vetted, let the parameters satisfy the standing assumptions with $d\in[0,1]$, and let $\pi$ be any production profit satisfying Assumptions D.1 and D.2. Let $\gamma_0\in\Gamma$ be such that for every $\gamma\in R^+(\gamma_0)$ and $i\in U_\gamma$, every dependent of $i$ other than $i$ in any state $\gamma'\in R^+(\gamma)$ is vetted and perfectly compliant (in $C$), and let every supplier in $C$ be vetted in $\gamma_0$. Then at every $\gamma\in R^+(\gamma_0)$ the policy
--   $$\xi^*(\gamma)=\begin{cases}\mathrm{ad}(i),&i\in U_\gamma,\ a+ud(\nabla(\gamma,i)-\hat uwz)<\hat c_{rp},\ \nabla(\gamma,i)\le\nabla(\gamma,i')\ \forall i'\in U_\gamma\\ \mathrm{rp},&a+ud(\nabla(\gamma,i)-\hat uwz)\ge\hat c_{rp}\ \forall i\in U_\gamma\end{cases}\qquad\text{(G.46)}$$
--   is optimal: $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$ in the first case and $\pi(\gamma)-\hat uwz|\hat S_g|-\hat c_{rp}|U_\gamma|=V^*(\gamma)$ in the second.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: R+(γ0): states reached with positive probability under some policy → Reach γ0: reflexive-transitive closure of γ ↦ γ⊕i, γ⊖i (i ∈ U_γ); reason: |U| strictly decreases along transitions, so every chain is realised by a stationary policy, and u ∈ (0,1) gives both outcomes of ad positive probability
--   - reading: Assumptions D.1, D.2 for any γ ∈ Γ → for every well-formed state; reason: Γ is the set of states over G
--   - reading: Definition D.1 lists the pairs (i ∈ S_a, i′ ∈ S_b) and (i = a, i′ = b) → both orders of each pair; reason: 'two suppliers are symmetric' is a symmetric relation; Assumption D.2 uses 'i′ and i are not symmetric'
--   - reading: any dependent of i in any state γ′ ∈ R+(γ) is vetted (perfectly compliant) → every dependent k ≠ i of i in γ′ is not in U_γ′ and lies in C; reason: i is a dependent of itself and is unaudited in γ, so the hypothesis is about the other dependents
--   - generalization: a fixed set Ŝ_g of not-perfectly-compliant suppliers (OA-40) → an arbitrary set C of suppliers perfectly compliant once vetted, Ŝ_g = S_g \ C; reason: the page leaves Ŝ_g general; every choice of the perfectly compliant suppliers is an instance
--   - reading: perfectly compliant suppliers (S_g ∖ Ŝ_g) in the setting of Theorem G.2, where they are 'vetted (perfectly compliant)' → hypothesis that C is disjoint from U_γ0 (hence from every U_γ, γ ∈ R+(γ0)); reason: (G.2) charges every unaudited supplier the probability u and (G.44) charges it ĉ_rp, so the model is the paper's only when every perfectly compliant supplier is vetted; without the hypothesis the Lean statement is false (one exclusive supplier i of firm a, a vetted, U = {i}, C = {a, i}, π constant: V* = π − min(uwz, a) while the rp value is π − ĉ_rp)
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-41, Theorem G.3, (G.46); (G.44) on OA-40

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_G_3 {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (C : Finset (Supplier ι)) (π : Network ι → ℝ) (hD1 : AssumptionD1 π) (hD2 : AssumptionD2 π)
    (γ₀ : State ι) (hγ₀ : WellFormedState γ₀) (hC : Disjoint γ₀.U C)
    (hdep : ∀ γ, Reach γ₀ γ → ∀ i ∈ γ.U, ∀ γ', Reach γ γ' → ∀ k ∈ γ'.g.dependents i, k ≠ i →
      k ∉ γ'.U ∧ k ∈ C) :
    ∀ γ, Reach γ₀ γ →
      (∀ i, IsLVUS π γ i →
        P.a + P.u * d * (nabla π γ i - uhat P d * P.w * P.z) < crpHat P d →
        QstarG P d C π γ (.ad i) = VstarG P d C π γ) ∧
      ((∀ i ∈ γ.U, crpHat P d ≤ P.a + P.u * d * (nabla π γ i - uhat P d * P.w * P.z)) →
        rpValueG P d C π γ = VstarG P d C π γ) := by sorry

end SRAudit.TwoPhase.Supplement
