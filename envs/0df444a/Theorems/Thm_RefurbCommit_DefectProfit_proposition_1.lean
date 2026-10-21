-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_1
-- name    : RefurbCommit.DefectProfit.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:47.015829+00:00
-- url     : https://prove2.me/theorems/68072613-771b-4079-8bb7-48583fffa90b
-- title:
--   Proposition 1, p. 10 (PDF 11) — the optimal second-period strategy (None / New Only / Refurbished Only / Product Line) is decided by ᾱ, q̲1, q̄1
-- statement:
--   Fix parameters satisfying the standing assumptions, a defect rate $\alpha>0$ and first-period sales $q_1\in[0,1]$, and assume
--   $$v_r(c_n+h)-v_n(c_r+h)k_r>0 .$$
--   Let $\bar\alpha=\dfrac{c_rv_n-c_nv_r}{v_r(c_n+h)-v_n(c_r+h)k_r}$, $\underline q_1=\max\Big\{\dfrac{\mu_n-\mu_r}{v_n-v_r},\ \dfrac{\mu_n(1+k_r\alpha)}{v_n(1+k_r\alpha)+2\alpha v_r}\Big\}$ and $\bar q_1=\max\{\mu_n/v_n,\ \mu_r/v_r\}$. Then the second-period problem (4.3) has an optimal price vector, $\underline q_1<\bar q_1$ whenever $\alpha>\bar\alpha$ and $\mu_r>0$, and every optimal price vector yields second-period sales $(q_2,q_r)$ with:
--
--   1. (None) $q_2=q_r=0$ if $q_1\ge\bar q_1$;
--   2. (New Only) $q_2>0$, $q_r=0$ if $\alpha\le\bar\alpha$ and $q_1<\bar q_1$;
--   3. (Refurbished Only) $q_2=0$, $q_r>0$ if $\alpha>\bar\alpha$, $q_1>0$ and $\underline q_1\le q_1<\bar q_1$;
--   4. (Product Line) $q_2>0$, $q_r>0$ if $\alpha>\bar\alpha$, $q_1>0$ and $q_1<\underline q_1$.
--
--   This is the second-period building block of the subgame-perfect equilibrium: it tells which products the firm offers after selling $q_1$ new units.
--
--   **Formalization Note** Three hypotheses are added to the page. (a) The positive denominator of $\bar\alpha$: the proof's equivalence $\alpha\lessgtr\bar\alpha\iff\mu_n/v_n\gtrless\mu_r/v_r$ (p. A-1) needs it; it holds automatically when $k_r<v_r/v_n$. (b) $\mu_r>0$ for the ordering $\underline q_1<\bar q_1$: when $\alpha>\bar\alpha$ and $\mu_r\le 0$ both thresholds are non-positive, every $q_1\ge 0$ falls under case (i), and the ordering can fail (an explicit standing instance is checked). (c) $q_1>0$ in cases (iii) and (iv): with $q_1=0$ there are no returns, so the constraint $(1+k_r\alpha)q_r\le\alpha q_1$ forces $q_r=0$. Optimality is stated for every optimal price vector; quantities at the optimum are unique because $\Pi_2$ is strictly concave in $(q_2,q_r)$.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. 10 (PDF 11), Proposition 1; thresholds from the proof, pp. A-1–A-2 (PDF 34–35)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 1 (p. 10), with the thresholds of its proof (p. A-1). Added hypotheses:
`hD` (positive denominator of ᾱ), `0 < µr` for the ordering `q̲1 < q̄1`, and `0 < q1`
for the two cases in which refurbished units are sold. -/
theorem proposition_1 (P : Params) (hP : P.Standing)
    (hD : 0 < P.vr * (P.cn + P.h) - P.vn * (P.cr + P.h) * P.kr)
    (α : ℝ) (hα : 0 < α) (q1 : ℝ) (hq0 : 0 ≤ q1) (hq1 : q1 ≤ 1) :
    (∃ p2 pr, IsOpt2 P α q1 p2 pr) ∧
    (alphaBar P < α → 0 < mur P α → qLow P α < qBar P α) ∧
    ∀ p2 pr, IsOpt2 P α q1 p2 pr →
      -- (i) None
      (qBar P α ≤ q1 → q2 P α q1 p2 pr = 0 ∧ qr P α q1 p2 pr = 0) ∧
      -- (ii) New Only
      (α ≤ alphaBar P → q1 < qBar P α → 0 < q2 P α q1 p2 pr ∧ qr P α q1 p2 pr = 0) ∧
      -- (iii) Refurbished Only
      (alphaBar P < α → 0 < q1 → qLow P α ≤ q1 → q1 < qBar P α →
        q2 P α q1 p2 pr = 0 ∧ 0 < qr P α q1 p2 pr) ∧
      -- (iv) Product Line
      (alphaBar P < α → 0 < q1 → q1 < qLow P α →
        0 < q2 P α q1 p2 pr ∧ 0 < qr P α q1 p2 pr) := by sorry

end RefurbCommit.DefectProfit
