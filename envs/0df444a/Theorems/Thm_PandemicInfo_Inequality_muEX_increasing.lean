-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_muEX_increasing
-- name    : PandemicInfo.Inequality.muEX_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:02.307868+00:00
-- url     : https://prove2.me/theorems/453d0305-95d2-4b6c-bd54-9cc5b9029fe7
-- title:
--   Proof of Theorem 2, p. 27 (PDF 28) — $\mu^{EX}_\lambda$ increasing in $\gamma$
-- statement:
--   Let $\sigma<\sigma'$ and keep every other parameter fixed, with the standing assumptions holding at both inequality levels; write $\gamma=2\sigma\sqrt3<\gamma'=2\sigma'\sqrt3$. If $\lambda$ lies in the exaggerating regime EX ($\lambda\in[0,1/2)$, $G_\ell(\lambda)>\kappa/\gamma>G_2(\lambda)$) at both levels, then
--
--   $$\mu^{EX}_\lambda(\gamma)<\mu^{EX}_\lambda(\gamma').$$
--
--   Through (18) this makes the optimal exaggeration probability decreasing in $\sigma$.
--
--   **Formalization Note** All statements assume the standing assumptions of §2, bundled in `Params.Standing`: $0<\omega_\ell<\omega_h<1$, $0<\rho^\circ<1$, $\theta\ge\sigma\sqrt3>0$, $\kappa>0$ and $\omega_\ell\kappa\ge\inf\mathcal C$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 27 (PDF 28), proof of Theorem 2, (56)–(58)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Proof of Theorem 2, p. 27: in the exaggerating regime EX, `µ^EX_λ` is increasing in
`γ = 2σ√3` (all other parameters fixed). -/
theorem muEX_increasing (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing)
    (hS' : ({ P with σ := σ' } : Params).Standing) (lam : ℝ)
    (hEX : P.EX lam) (hEX' : ({ P with σ := σ' } : Params).EX lam) :
    P.μEX lam < ({ P with σ := σ' } : Params).μEX lam := by sorry

end PandemicInfo.Inequality
