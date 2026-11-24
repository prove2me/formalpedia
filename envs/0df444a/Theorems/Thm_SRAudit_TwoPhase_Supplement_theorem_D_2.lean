-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_D_2
-- name    : SRAudit.TwoPhase.Supplement.theorem_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:37:02.002008+00:00
-- url     : https://prove2.me/theorems/3c715d9b-c636-4066-8ed7-1a9689daa0d9
-- title:
--   Theorem D.2, OA-19 — under Condition 1 with tier 1 vetted, the policy ξ** of (D.80) away from γ1 and the weighted threshold (D.81) at γ1 is optimal
-- statement:
--   In the setting of Theorem 4 (standing parameters, Cournot profit $\pi$ with capacity $M$ large enough, Condition 1), the policy $\xi^{**}$ is optimal at every state of $\Gamma$ in which every tier-1 firm is vetted:
--
--   1. **(D.80)** at a nonterminal state $\gamma\ne\gamma_1$ with an LVUS $i$: $\mathrm{ad}(i)$ is optimal if $u\nabla(\gamma,i)+a<c_{rp}$, and rp is optimal if $u\nabla(\gamma,i)+a\ge c_{rp}$;
--   2. **(D.81)** at $\gamma_1$, for $i\in U_{\gamma_1}$: $\mathrm{ad}(i)$ is optimal if
--   $$\frac{1}{1+u}\bigl(a+u\nabla(\gamma_1,i)\bigr)+\frac{u}{1+u}\bigl(a+u\pi(\gamma_1\ominus i)\bigr)<c_{rp},$$
--   and rp is optimal if the left side is $\ge c_{rp}$.
--
--   Optimality of $\mathrm{ad}(i)$ means $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$, of rp that $\pi(\gamma)-c_{rp}|U_\gamma|=V^*(\gamma)$. Theorem 4 is part 1.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - reading: π(γ) is π*_c in the equilibrium of g, 0 at g∅ → cournotProfit E M: the buyer's profit in the unique equilibrium, 0 at a null network; reason: definition on p. 15 and fn. 6; the junk value off uniqueness never arises on well-formed networks by Theorem 1
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: Condition 1: for any i, i′ ∈ U_γ, ∇(γ,i′) ≤ ∇(γ⊖i,i′) → for distinct i ≠ i′, over well-formed states; reason: for i = i′ the right side is ∇(γ⊖i,i) = 0 and the condition would fail for every profit increasing in suppliers, making the theorem vacuous; Condition 1 is the tier-1-vetted case of Assumption D.1, which has i′ ∉ D(i) and so i′ ≠ i
--   - encoding: the state γ1 = ({a,b},{1},{2},∅) with U = {1,2} → IsGamma1: the same shape for any two distinct labels; reason: fn. 9 names the two tier-2 suppliers 1 and 2; any labels give the same state up to renaming
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-19, Theorem D.2, (D.80), (D.81)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production
import Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_D_2 {ι : Type} [DecidableEq ι] (P : Params) (hP : P.Standing) (E : Demand)
    (hE : E.Standing) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    Condition1 (cournotProfit E M : Network ι → ℝ) →
    -- (D.80): nonterminal states `γ ≠ γ1` with every tier-1 firm vetted, `i` an LVUS
    (∀ γ : State ι, WellFormedState γ → Tier1Vetted γ → ¬ IsGamma1 γ →
      ∀ i, IsLVUS (cournotProfit E M) γ i →
        (P.u * nabla (cournotProfit E M) γ i + P.a < crp P →
          Qstar P (cournotProfit E M) γ (.ad i) = Vstar P (cournotProfit E M) γ) ∧
        (crp P ≤ P.u * nabla (cournotProfit E M) γ i + P.a →
          rpValue P (cournotProfit E M) γ = Vstar P (cournotProfit E M) γ)) ∧
    -- (D.81): the state `γ1`
    (∀ γ : State ι, IsGamma1 γ → ∀ i ∈ γ.U,
      (1 / (1 + P.u) * (P.a + P.u * nabla (cournotProfit E M) γ i) +
          P.u / (1 + P.u) * (P.a + P.u * cournotProfit E M (drop γ i).g) < crp P →
        Qstar P (cournotProfit E M) γ (.ad i) = Vstar P (cournotProfit E M) γ) ∧
      (crp P ≤ 1 / (1 + P.u) * (P.a + P.u * nabla (cournotProfit E M) γ i) +
          P.u / (1 + P.u) * (P.a + P.u * cournotProfit E M (drop γ i).g) →
        rpValue P (cournotProfit E M) γ = Vstar P (cournotProfit E M) γ)) := by sorry

end SRAudit.TwoPhase.Supplement
