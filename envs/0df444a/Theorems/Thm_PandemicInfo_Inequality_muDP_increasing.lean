-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_muDP_increasing
-- name    : PandemicInfo.Inequality.muDP_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:16.30331+00:00
-- url     : https://prove2.me/theorems/d812d96e-17f3-4ea2-a20f-b0790c5daf9d
-- title:
--   Proof of Theorem 2, pp. 26–27 (PDF 27–28) — $\mu^{DP}_\lambda$ increasing in $\gamma$
-- statement:
--   Let $\sigma<\sigma'$ and keep every other parameter fixed, with the standing assumptions holding at both inequality levels; write $\gamma=2\sigma\sqrt3<\gamma'=2\sigma'\sqrt3$. If $\lambda$ lies in the downplaying regime DP ($\lambda\in(4/5,1]$, $G_1(\lambda)>\kappa/\gamma>G_h(\lambda)$) at both levels, then
--
--   $$\mu^{DP}_\lambda(\gamma)<\mu^{DP}_\lambda(\gamma').$$
--
--   Through (17) this makes the optimal downplaying probability increasing in $\sigma$.
--
--   **Formalization Note** All statements assume the standing assumptions of §2, bundled in `Params.Standing`: $0<\omega_\ell<\omega_h<1$, $0<\rho^\circ<1$, $\theta\ge\sigma\sqrt3>0$, $\kappa>0$ and $\omega_\ell\kappa\ge\inf\mathcal C$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), pp. 26–27 (PDF 27–28), proof of Theorem 2, (50)–(55)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Proof of Theorem 2, pp. 26–27: in the downplaying regime DP, `µ^DP_λ` is increasing in
`γ = 2σ√3` (all other parameters fixed). -/
theorem muDP_increasing (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing)
    (hS' : ({ P with σ := σ' } : Params).Standing) (lam : ℝ)
    (hDP : P.DP lam) (hDP' : ({ P with σ := σ' } : Params).DP lam) :
    P.μDP lam < ({ P with σ := σ' } : Params).μDP lam := by sorry

end PandemicInfo.Inequality
