-- Prove2me | Theorems.Thm_SRAudit_TwoPhase_Supplement_proposition_G_2
-- name    : SRAudit.TwoPhase.Supplement.proposition_G_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:39:29.1839+00:00
-- url     : https://prove2.me/theorems/6518238b-08d6-42b6-ba51-d3d0d0a819c5
-- title:
--   Proposition G.2, OA-39 — with inaccurate audits and only ar/pp allowed, rectify all if a + udr ≤ (u − û)wz, produce if ≥, and V*(γ) is (G.29)
-- statement:
--   In the inaccurate-audit model of Appendix G with $C=\emptyset$ (standing parameters, $d\in[0,1]$, any production profit $\pi$ of the network), limit the buyer's actions to $\mathrm{ar}$ and $\mathrm{pp}$. For every state $\gamma$:
--   $$V^*(\gamma)=\pi(\gamma)-\hat uwz|S_{g_\gamma}|-\{(a+udr)\wedge[(u-\hat u)wz]\}\,|U_\gamma|,\qquad\text{(G.29)}$$
--   every $\mathrm{ar}(i)$, $i\in U_\gamma$, is optimal if $a+udr\le(u-\hat u)wz$, and $\mathrm{pp}$ is optimal if $a+udr\ge(u-\hat u)wz$. It replaces Proposition D.2 in the proof of Theorem G.1.
--
--   Differences from the source:
--   - reading: a production profit π(γ) (§6.1, OA-53) → an arbitrary function π of the network; reason: the proofs use only that π(γ) depends on γ through g ((D.27)); §6.1 (p. 27) says the result does not depend on the competition model
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-39, Proposition G.2, (G.29)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

theorem proposition_G_2 {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (π : Network ι → ℝ) (γ : State ι) :
    VarG P d ∅ π γ = π γ.g - uhat P d * P.w * P.z * γ.g.suppliers.card -
      min (P.a + P.u * d * P.r) ((P.u - uhat P d) * P.w * P.z) * γ.U.card ∧
    (P.a + P.u * d * P.r ≤ (P.u - uhat P d) * P.w * P.z →
      ∀ i ∈ γ.U, QarG P d ∅ π γ (.ar i) = VarG P d ∅ π γ) ∧
    ((P.u - uhat P d) * P.w * P.z ≤ P.a + P.u * d * P.r →
      QarG P d ∅ π γ .pp = VarG P d ∅ π γ) := by sorry

end SRAudit.TwoPhase.Supplement
