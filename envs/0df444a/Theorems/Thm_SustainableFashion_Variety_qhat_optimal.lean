-- Prove2me | Theorems.Thm_SustainableFashion_Variety_qhat_optimal
-- name    : SustainableFashion.Variety.qhat_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:36.907893+00:00
-- url     : https://prove2.me/theorems/ad3c106d-d308-4083-bf12-08ffcf375e3b
-- title:
--   §4.2, p. 14 — for given m and u, the optimal inventory is q̂ = n̄(1 − mk/k′) if k′ ≥ mk, 0 otherwise
-- statement:
--   Fix parameters with $0<k<k'$ and $\bar n>0$, a number of styles $m\ge1$ and a quality $u>0$. Among inventories $q\in[0,\bar n]$, a level $q$ maximises the expected profit $\mathbb E\Pi(m,u,\cdot)$ of problem (1) if and only if
--   $$q=\hat q=\begin{cases}\bar n\big(1-\frac{mk}{k'}\big), & k'\ge mk,\\ 0, & k'<mk.\end{cases}$$
--
--   This is the first step of the paper's backward induction: the per-style inventory falls as the number of styles grows, and the firm stocks nothing before the season once $m>k'/k$.
--
--   **Formalization Note** The hypothesis $u>0$ is necessary: at $u=0$ the profit does not depend on $q$ and every inventory is optimal. It does not restrict the paper's use of the display, since the optimal quality is positive.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), §4.2, display following "We solve the problem by backward induction", p. 14

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem qhat_optimal (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hn : 0 < P.nbar) (m u : ℝ) (hm : 1 ≤ m) (hu : 0 < u)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ P.nbar) :
    (∀ q', 0 ≤ q' → q' ≤ P.nbar → expProfit P m u q' ≤ expProfit P m u q) ↔
      q = (if m * P.k ≤ P.k' then P.nbar * (1 - m * P.k / P.k') else 0) := by sorry

end SustainableFashion.Variety
