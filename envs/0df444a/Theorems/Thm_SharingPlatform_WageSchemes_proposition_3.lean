-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_proposition_3
-- name    : SharingPlatform.WageSchemes.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:06.663246+00:00
-- url     : https://prove2.me/theorems/5818afc9-1743-4856-b6bf-38872d194358
-- title:
--   Proposition 3, pp. 16–17 (PDF 17–18) — the platform-profit ranking of the FW, FCR and DCR wage schemes (case (c) with (13) < 0)
-- statement:
--   Assume $a, b, c, k, l, m > 0$, Assumption 1 ($a/c > k/m$) and Assumption 2 ($l \le 2c + c^2/b$). Take
--   - any symmetric Nash equilibrium $((p, \alpha^{D*}), (p, \alpha^{D*}))$ of the dynamic-commission-rate game with positive demand and supply, with platform profit $\pi^{D*}$;
--   - any symmetric subgame-perfect equilibrium of the fixed-commission-rate game with positive on-path demand and supply, whose stage-2 price rules are continuous at the equilibrium pair, with on-path platform profit $\pi^{F*}$;
--   - any symmetric subgame-perfect equilibrium of the fixed-wage game with the same properties, with on-path platform profit $\pi^{W*}$.
--
--   Let $Q$ denote the left side of Inequality (13) evaluated at the DCR commission rate:
--
--   $$Q = \frac{b+c+l+m}{(b+c)(l+m)\alpha^{D*}} - \frac{b + (1-\alpha^{D*})l}{(1-\alpha^{D*})(cl-bm)}.$$
--
--   Then:
--   1. if $\frac{b}{c} > \frac{l}{m}$, then $\pi^{W*} > \pi^{F*} > \pi^{D*}$;
--   2. if $\frac{b}{c} < \frac{l}{m}$ and $Q > 0$, then $\pi^{F*} > \pi^{D*} > \pi^{W*}$;
--   3. if $\frac{b}{c} < \frac{l}{m}$ and $Q < 0$, then $\pi^{D*} > \pi^{F*} > \pi^{W*}$.
--
--   Which wage scheme the platforms prefer is thus decided by demand-side competition $b/c$ against supply-side competition $l/m$, and, when the supply side is more competitive, by condition (13).
--
--   **Formalization Note** The page states case (c) as "condition (13) does not hold", which includes $Q = 0$. At $Q = 0$ the FCR and DCR commission rates coincide and $\pi^{D*} = \pi^{F*}$, so the strict ranking fails there. The statement uses $Q < 0$. The volume is $\max\{0,\min\{d_i,s_i\}\}$. Equilibria are required to have positive demand and supply (p. 9). The two-stage equilibria are required to have stage-2 price rules continuous at the equilibrium pair. Without that condition, FCR equilibria sustained by zero-profit punishments exist at commission rates other than Lemma 2's, and the ranking fails. $Q$ has nonzero denominators here: $0 < \alpha^{D*} < 1$ by Lemma 1, and $cl - bm > 0$ in cases 2 and 3. Profits are platform 1's; in a symmetric equilibrium both platforms earn the same.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, pp. 16–17 (PDF 17–18), Proposition 3, Inequality (13); proof A.8, pp. 51–53 (PDF 52–54)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem proposition_3 (P : Params) (hP : P.Standing)
    (xD : ℝ × ℝ) (hD : IsNashDCR P xD xD) (hDn : NontrivialDCR P xD xD)
    (eF : TwoStage) (hF : IsSPE P fcrWage eF) (hFc : eF.OnPathContinuous)
    (hFs : eF.IsSymmetric) (hFn : eF.Nontrivial P fcrWage)
    (eW : TwoStage) (hW : IsSPE P fwWage eW) (hWc : eW.OnPathContinuous)
    (hWs : eW.IsSymmetric) (hWn : eW.Nontrivial P fwWage) :
    (P.l / P.m < P.b / P.c →
      profitDCR P xD xD < eF.onPathProfit P fcrWage ∧
        eF.onPathProfit P fcrWage < eW.onPathProfit P fwWage) ∧
    (P.b / P.c < P.l / P.m → 0 < cond13 P xD.2 →
      eW.onPathProfit P fwWage < profitDCR P xD xD ∧
        profitDCR P xD xD < eF.onPathProfit P fcrWage) ∧
    (P.b / P.c < P.l / P.m → cond13 P xD.2 < 0 →
      eW.onPathProfit P fwWage < eF.onPathProfit P fcrWage ∧
        eF.onPathProfit P fcrWage < profitDCR P xD xD) := by sorry
end SharingPlatform.WageSchemes
