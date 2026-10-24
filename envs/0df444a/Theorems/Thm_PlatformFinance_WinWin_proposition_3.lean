-- Prove2me | Theorems.Thm_PlatformFinance_WinWin_proposition_3
-- name    : PlatformFinance.WinWin.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:25.157199+00:00
-- url     : https://prove2.me/theorems/cf8fe618-b8cf-4e88-8a85-71210b2b5aaa
-- title:
--   Proposition 3, p. 15 — below r̂₁(δ) platform financing lowers the seller's unit cost and raises her order; above it, the reverse
-- statement:
--   Under the standing conditions ($0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$, $r>-1$, $c(1+r)<(a+\delta)(1-\varphi)$), let $(w^T,q^T)$ be the equilibrium price and order of any subgame-perfect equilibrium of the trade-credit game, $(w^P,q^P)$ those of any subgame-perfect equilibrium of the platform-financing game at rate $r$, and $\hat r_1(\delta)$ the threshold of p. 15. Write $\bar\delta=((1-\varphi)a-c(1+r_f))/(1-\varphi)$. Then
--   1. if $r<\hat r_1(\delta)$, then $w^P(1+r)<w^T$ and $q^P>q^T$;
--   2. if $r>\hat r_1(\delta)$, or $r=\hat r_1(\delta)$ with $\delta\le\delta_2$ or $\delta>\delta_3$, then $w^P(1+r)\ge w^T$ and $q^P\le q^T$;
--   3. $\hat r_1(\delta)=r_f$ when $\delta\le\delta_2$;
--   4. $\hat r_1(\delta)<r_f$ when $\delta_2<\delta<\bar\delta$;
--   5. $\hat r_1(\delta)>r_f$ when $\delta>\bar\delta$.
--
--   **Formalization Note.** The boundary rate $r=\hat r_1(\delta)$ is kept in item 2 where the page's claim holds there ($\delta\le\delta_2$, where $r=r_f$ and both schemes coincide; $\delta>\delta_3$, where $r=r_2$ and $w^P(1+r)=w^T$, $q^P=q^T$), and excluded only for $\delta_2<\delta\le\delta_3$: there it is $r=r_1$, i.e. $\delta=\delta_r$, where Proposition 2 places platform financing in its no-default branch and $w^P(1+r)<w^T$, contradicting the page's "otherwise"; the proof (p. 37) uses the other branch there. Item 4 uses the strict $\delta<\bar\delta$ of the proof (p. 38): the statement prints $\delta\le\bar\delta$, but at $\delta=\bar\delta$ one has $\hat r_1=r_2=r_f$.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 15, Proposition 3 (r̂₁ defined on p. 15); proof pp. 36–38

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.WinWin
theorem proposition_3 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    (r < rhat1 a δ φ c rf →
        σP.w * (1 + r) < σT.w ∧ σT.order σT.w < σP.order σP.w) ∧
      (rhat1 a δ φ c rf < r ∨
          (r = rhat1 a δ φ c rf ∧ (δ ≤ delta2 a φ c rf ∨ delta3 a φ c rf < δ)) →
        σT.w ≤ σP.w * (1 + r) ∧ σP.order σP.w ≤ σT.order σT.w) ∧
      (δ ≤ delta2 a φ c rf → rhat1 a δ φ c rf = rf) ∧
      (delta2 a φ c rf < δ → δ < K0 a φ c rf / (1 - φ) → rhat1 a δ φ c rf < rf) ∧
      (K0 a φ c rf / (1 - φ) < δ → rf < rhat1 a δ φ c rf) := by sorry
end PlatformFinance.WinWin
