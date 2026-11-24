-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_4
-- name    : SRAudit.TwoPhase.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:35:11.809596+00:00
-- url     : https://prove2.me/theorems/17ba10ab-6470-446a-8976-8ca397d465f5
-- title:
--   Theorem 4, p. 22 — with tier 1 vetted and Condition 1, audit and drop an LVUS i if a + u∇(γ,i) < crp, else proceed to the rp subphase
-- statement:
--   Take the auditing model of §3.2 with standing parameters ($a,r\ge0$, $u\in(0,1)$, $w\in(0,1]$, $z\ge0$) and the Cournot production profit $\pi=\pi^*_c$ ($\beta>0$, $\alpha\ge v_T$), with capacity $M$ large enough. Assume Condition 1. Let $\gamma\ne\gamma_1$ be a state of $\Gamma$ in which every tier-1 firm is vetted, and let $i$ be an LVUS in $\gamma$, i.e. $\nabla(\gamma,i)\le\nabla(\gamma,i')$ for all $i'\in U_\gamma$, where $\nabla(\gamma,i)=\pi(\gamma)-\pi(\gamma\ominus i)$. Then:
--
--   1. if $a+u\nabla(\gamma,i)<c_{rp}$, auditing and dropping $i$ is optimal: $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$;
--   2. if $a+u\nabla(\gamma,i)\ge c_{rp}$, proceeding to the rp subphase is optimal: $\pi(\gamma)-c_{rp}|U_\gamma|=V^*(\gamma)$,
--
--   where $c_{rp}=(uwz)\wedge(a+ur)$. The buyer keeps trimming the side of the network with the least valuable supplier until even that supplier is worth more than its expected rp cost.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - reading: π(γ) is π*_c in the equilibrium of g, 0 at g∅ → cournotProfit E M: the buyer's profit in the unique equilibrium, 0 at a null network; reason: definition on p. 15 and fn. 6; the junk value off uniqueness never arises on well-formed networks by Theorem 1
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: Condition 1: for any i, i′ ∈ U_γ, ∇(γ,i′) ≤ ∇(γ⊖i,i′) → for distinct i ≠ i′, over well-formed states; reason: for i = i′ the right side is ∇(γ⊖i,i) = 0 and the condition would fail for every profit increasing in suppliers, making the theorem vacuous; Condition 1 is the tier-1-vetted case of Assumption D.1, which has i′ ∉ D(i) and so i′ ≠ i
--   - encoding: the state γ1 = ({a,b},{1},{2},∅) with U = {1,2} → IsGamma1: the same shape for any two distinct labels; reason: fn. 9 names the two tier-2 suppliers 1 and 2; any labels give the same state up to renaming
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 22, Theorem 4 (Condition 1 and fn. 9, p. 21; Definition 1, p. 22)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production
import Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_4 {ι : Type} [DecidableEq ι] (P : Params) (hP : P.Standing) (E : Demand)
    (hE : E.Standing) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    Condition1 (cournotProfit E M : Network ι → ℝ) →
    ∀ γ : State ι, WellFormedState γ → Tier1Vetted γ → ¬ IsGamma1 γ →
    ∀ i, IsLVUS (cournotProfit E M) γ i →
      (P.a + P.u * nabla (cournotProfit E M) γ i < crp P →
        Qstar P (cournotProfit E M) γ (.ad i) = Vstar P (cournotProfit E M) γ) ∧
      (crp P ≤ P.a + P.u * nabla (cournotProfit E M) γ i →
        rpValue P (cournotProfit E M) γ = Vstar P (cournotProfit E M) γ) := by sorry

end SRAudit.TwoPhase.Supplement
