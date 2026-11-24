-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_theorem_G_4
-- name    : SRAudit.TwoPhase.Supplement.theorem_G_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:43:15.135075+00:00
-- url     : https://prove2.me/theorems/7057a42c-0776-4bd4-bee4-2d786f8fbbc0
-- title:
--   Theorem G.4, OA-46 — inaccurate audits, Condition 1, tier 1 vetted: the policy (G.92) away from γ1 and the weighted threshold (G.93) at γ1 is optimal
-- statement:
--   In the setting of Theorem G.2 ($C=S(1)$, standing parameters, $d\in[0,1]$, Cournot profit with capacity $M$ large enough, Condition 1) the policy $\xi^{**}$ is optimal at every state of $\Gamma$ in which every tier-1 firm is vetted:
--   1. **(G.92)** at a nonterminal $\gamma\ne\gamma_1$ with an LVUS $i$: $\mathrm{ad}(i)$ if $a+ud(\nabla(\gamma,i)-\hat uwz)<\hat c_{rp}$, rp if $\ge$;
--   2. **(G.93)** at $\gamma_1$, for $i\in U_{\gamma_1}$: $\mathrm{ad}(i)$ if
--   $$\frac{1}{1+ud}\bigl[a+ud(\nabla(\gamma_1,i)-\hat uwz)\bigr]+\frac{ud}{1+ud}\bigl[a+ud(\pi(\gamma_1\ominus i)-\hat uwz)\bigr]<\hat c_{rp},$$
--   rp if the left side is $\ge\hat c_{rp}$.
--
--   Optimality of $\mathrm{ad}(i)$ means $\widetilde V^*(\gamma,\mathrm{ad}(i))=V^*(\gamma)$, of rp that $\pi(\gamma)-\hat uwz|\hat S_g|-\hat c_{rp}|U_\gamma|=V^*(\gamma)$.
--
--   Differences from the source:
--   - reading: a production model with an (arbitrarily large) capacity M > 0 → ∃ M₀ > 0 such that the statement holds for every M ≥ M₀; reason: the closed forms of Proposition C.5, on which the proof rests, ignore the upper bound s ≤ M (OA-7–OA-8); they are the equilibrium once M exceeds every closed-form quantity, e.g. M₀ = (α − v_T)/β, uniformly over networks
--   - reading: π(γ) is π*_c in the equilibrium of g, 0 at g∅ → cournotProfit E M: the buyer's profit in the unique equilibrium, 0 at a null network; reason: definition on p. 15 and fn. 6; the junk value off uniqueness never arises on well-formed networks by Theorem 1
--   - reading: it is optimal to take action x at γ / the policy ξ* is optimal at γ → x attains V*(γ): Ṽ*(γ, ad(i)) = V*(γ) for ad(i), Ṽ*(γ, rp) = π(γ) − c_rp|U_γ| = V*(γ) for rp; reason: rp is the shorthand of p. 20 / OA-11 whose value is Ṽ*(γ, rp); optimality is the argmax criterion of p. 11
--   - reading: Condition 1: for any i, i′ ∈ U_γ, ∇(γ,i′) ≤ ∇(γ⊖i,i′) → for distinct i ≠ i′, over well-formed states; reason: for i = i′ the right side is ∇(γ⊖i,i) = 0 and the condition would fail for every profit increasing in suppliers, making the theorem vacuous; Condition 1 is the tier-1-vetted case of Assumption D.1, which has i′ ∉ D(i) and so i′ ≠ i
--   - encoding: the state γ1 = ({a,b},{1},{2},∅) with U = {1,2} → IsGamma1: the same shape for any two distinct labels; reason: fn. 9 names the two tier-2 suppliers 1 and 2; any labels give the same state up to renaming
--   - reading: networks g ∈ G → networks satisfying WellFormedNet; reason: the published Network type admits tuples outside G (an absent firm with suppliers, shared suppliers with one firm); G is the set of networks of (C.36)
--   - encoding: tier-1 firms vetted (perfectly compliant) → C = S(1) in ζ and in the rp value, with every tier-1 firm vetted; reason: OA-40
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-46, Theorem G.4, (G.92), (G.93)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production
import Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem theorem_G_4 {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (E : Demand) (hE : E.Standing) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    Condition1 (cournotProfit E M : Network ι → ℝ) →
    -- (G.92): nonterminal states `γ ≠ γ1` with every tier-1 firm vetted, `i` an LVUS
    (∀ γ : State ι, WellFormedState γ → Tier1Vetted γ → ¬ IsGamma1 γ →
      ∀ i, IsLVUS (cournotProfit E M) γ i →
        (P.a + P.u * d * (nabla (cournotProfit E M) γ i - uhat P d * P.w * P.z) < crpHat P d →
          QstarG P d tier1Set (cournotProfit E M) γ (.ad i) =
            VstarG P d tier1Set (cournotProfit E M) γ) ∧
        (crpHat P d ≤ P.a + P.u * d * (nabla (cournotProfit E M) γ i - uhat P d * P.w * P.z) →
          rpValueG P d tier1Set (cournotProfit E M) γ =
            VstarG P d tier1Set (cournotProfit E M) γ)) ∧
    -- (G.93): the state `γ1`
    (∀ γ : State ι, IsGamma1 γ → ∀ i ∈ γ.U,
      (1 / (1 + P.u * d) *
            (P.a + P.u * d * (nabla (cournotProfit E M) γ i - uhat P d * P.w * P.z)) +
          P.u * d / (1 + P.u * d) *
            (P.a + P.u * d * (cournotProfit E M (drop γ i).g - uhat P d * P.w * P.z)) <
          crpHat P d →
        QstarG P d tier1Set (cournotProfit E M) γ (.ad i) =
          VstarG P d tier1Set (cournotProfit E M) γ) ∧
      (crpHat P d ≤
          1 / (1 + P.u * d) *
            (P.a + P.u * d * (nabla (cournotProfit E M) γ i - uhat P d * P.w * P.z)) +
          P.u * d / (1 + P.u * d) *
            (P.a + P.u * d * (cournotProfit E M (drop γ i).g - uhat P d * P.w * P.z)) →
        rpValueG P d tier1Set (cournotProfit E M) γ =
          VstarG P d tier1Set (cournotProfit E M) γ)) := by sorry

end SRAudit.TwoPhase.Supplement
