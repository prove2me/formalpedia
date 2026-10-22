-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_proposition_D_2
-- name    : SRAudit.TwoPhase.proposition_D_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:37.52925+00:00
-- url     : https://prove2.me/theorems/71a3b172-e6ce-4bfd-a8e8-b69b56a0cc16
-- title:
--   Proposition D.2, OA-13 — value of the rectify-or-produce problem
-- statement:
--   Restrict an admissible auditing policy to proceeding to production ($pp$) or auditing and rectifying an unaudited supplier ($ar(i)$). For a state $\gamma=(g,U_\gamma)$, let $V_{ar}(\gamma)$ be the optimal restricted value and set $c_{rp}=\min\{uwz,a+ur\}$. Under the paper's cost and probability assumptions,
--
--   $$
--   V_{ar}(\gamma)=\pi(g)-c_{rp}|U_\gamma|.
--   $$
--
--   If $a+ur\leq uwz$, every available $ar(i)$ is optimal, so the remaining suppliers may be rectified in any sequence. If $a+ur\geq uwz$, proceeding to production is optimal. Both conclusions apply at equality.
--
--   **Formalization Note** The $V^*$ in display (D.25) is the restricted problem's optimal value. Production profit is allowed to be any function of the network; the paper notes this structural result does not depend on the mode of competition.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-13 (PDF 48), Proposition D.2 and (D.25)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase

theorem proposition_D_2 {ι : Type} [DecidableEq ι] (P : Params)
    (hP : P.Standing) (π : Network ι → ℝ) (γ : State ι) :
    Var P π γ = π γ.g - crp P * γ.U.card ∧
    (P.a + P.u * P.r ≤ P.u * P.w * P.z →
      ∀ i ∈ γ.U, Qar P π γ (.ar i) = Var P π γ) ∧
    (P.u * P.w * P.z ≤ P.a + P.u * P.r →
      Qar P π γ .pp = Var P π γ) := by sorry

end SRAudit.TwoPhase
