-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_F_1
-- name    : SRAudit.TwoPhase.Supplement.proposition_F_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:37:41.579842+00:00
-- url     : https://prove2.me/theorems/26798190-fa28-4dad-bca0-0798096ed4b7
-- title:
--   Proposition F.1, OA-29 — with tier-dependent penalties and only ar/pp allowed, rectify exactly the tiers k with a + ur ≤ uwz_k, and V*(γ) is (F.1)
-- statement:
--   In the model of Appendix F (penalties $z_1$ for tier 1 and $z_2$ for tier 2, standing parameters, any production profit $\pi$ of the network), limit the buyer's actions to $\mathrm{ar}$ and $\mathrm{pp}$, and let $V^*$ be the resulting optimal value. For every state $\gamma$:
--   $$V^*(\gamma)=\pi(\gamma)-[(uwz_1)\wedge(a+ur)]\,|U_\gamma\cap S(1)|-[(uwz_2)\wedge(a+ur)]\,|U_\gamma\cap S(2)|,\qquad\text{(F.1)}$$
--   and the following policy is optimal at $\gamma$:
--   1. **(a)** if $a+ur\le uwz_1$ and $a+ur\le uwz_2$: $\mathrm{ar}(i)$ for any unaudited $i$;
--   2. **(b)** if $a+ur\le uwz_1$ and $a+ur>uwz_2$: $\mathrm{ar}(i)$ for any unaudited tier-1 $i$, and $\mathrm{pp}$ once no tier-1 supplier is unaudited;
--   3. **(c)** if $a+ur>uwz_1$ and $a+ur\le uwz_2$: the same with tiers exchanged;
--   4. **(d)** if $a+ur>uwz_1$ and $a+ur>uwz_2$: $\mathrm{pp}$.
--
--   It replaces Proposition D.2 in the proof of Theorem F.1.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
--   - reading: the policy 'audit and rectify all remaining … in any sequence, then proceed to production' is optimal → at every state the prescribed action attains the restricted optimal value; reason: optimality of a policy is the argmax criterion of p. 11 at every state
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-29, Proposition F.1, (F.1)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Heterogeneous

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_F_1 {ι : Type} [DecidableEq ι] (P : ParamsF) (hP : P.Standing)
    (π : Network ι → ℝ) (γ : State ι) :
    -- (F.1)
    VarF P π γ = π γ.g - min (P.u * P.w * P.z1) (P.a + P.u * P.r) * (γ.U.filter IsTier1).card -
      min (P.u * P.w * P.z2) (P.a + P.u * P.r) * (γ.U.filter (fun i => ¬ IsTier1 i)).card ∧
    -- (a)
    (P.a + P.u * P.r ≤ P.u * P.w * P.z1 → P.a + P.u * P.r ≤ P.u * P.w * P.z2 →
      ∀ i ∈ γ.U, QarF P π γ (.ar i) = VarF P π γ) ∧
    -- (b)
    (P.a + P.u * P.r ≤ P.u * P.w * P.z1 → P.u * P.w * P.z2 < P.a + P.u * P.r →
      (∀ i ∈ γ.U, IsTier1 i → QarF P π γ (.ar i) = VarF P π γ) ∧
      ((∀ i ∈ γ.U, ¬ IsTier1 i) → QarF P π γ .pp = VarF P π γ)) ∧
    -- (c)
    (P.u * P.w * P.z1 < P.a + P.u * P.r → P.a + P.u * P.r ≤ P.u * P.w * P.z2 →
      (∀ i ∈ γ.U, ¬ IsTier1 i → QarF P π γ (.ar i) = VarF P π γ) ∧
      ((∀ i ∈ γ.U, IsTier1 i) → QarF P π γ .pp = VarF P π γ)) ∧
    -- (d)
    (P.u * P.w * P.z1 < P.a + P.u * P.r → P.u * P.w * P.z2 < P.a + P.u * P.r →
      QarF P π γ .pp = VarF P π γ) := by sorry

end SRAudit.TwoPhase.Supplement
