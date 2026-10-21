-- Prove2me | Theorems.Thm_RefurbCommit_DefectProfit_proposition_7
-- name    : RefurbCommit.DefectProfit.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:50.354988+00:00
-- url     : https://prove2.me/theorems/b2df9b59-a5b5-4608-867e-fed9c7a0d611
-- title:
--   Proposition 7, p. B-1 (PDF 42) — with commitment, q^C_2 = 0; refurbish none/some/all by ᾱ and v̄r
-- statement:
--   Fix parameters satisfying the standing assumptions with $v_r(c_n+h)-v_n(c_r+h)k_r>0$, and a defect rate $\alpha>0$ with positive commitment profit $\Pi^C(\alpha)>0$. Let
--   $$\bar\alpha=\frac{c_rv_n-c_nv_r}{v_r(c_n+h)-v_n(c_r+h)k_r},\qquad \bar v_r=\frac{A+\sqrt{A^2+4\rho\alpha v_n(1+k_r\alpha)(v_r-\mu_r)}}{2\rho\alpha},$$
--   where $A=\alpha(\mu_n+\rho(v_r-\mu_r))-(1+k_r\alpha)(v_n-\mu_n)$. Then an optimal committed price vector $(p_1,p_2,p_r)$ exists, and every optimal one has $q^C_2=0$ (no new units in period 2) and:
--
--   1. $q^C_r=0$ if $\alpha\le\bar\alpha$;
--   2. $\alpha q^C_1>(1+k_r\alpha)q^C_r>0$ (some returns refurbished) if $\alpha>\bar\alpha$ and $v_r<\bar v_r$;
--   3. $\alpha q^C_1=(1+k_r\alpha)q^C_r>0$ (all returns refurbished) if $\alpha>\bar\alpha$ and $v_r\ge\bar v_r$.
--
--   The proposition describes the commitment benchmark against which Proposition 3 measures the no-commitment profit; note that $v_r-\mu_r=(1+k_r\alpha)c_r+hk_r\alpha$, so $\bar v_r$ does not depend on $v_r$.
--
--   **Formalization Note** The positive denominator of $\bar\alpha$ is added, as in Proposition 1. $\Pi^C(\alpha)>0$ is the paper's positive-profit restriction (p. 6). Existence of an optimal price vector is stated as a conjunct (problem (B.20) is a maximization), so that the second clause is not vacuous.
-- source:
--   Singh, Ramachandran & Subramanian, Intertemporal product management with strategic consumers: the value of defective product returns, accepted manuscript (MSOM, Dec. 2020; SSRN 2511424), p. B-1 (PDF 42), Proposition 7; v̄r and A from the proof, p. B-2 (PDF 43); ᾱ from p. A-1 (PDF 34)

import Mathlib
import Definitions.Def_RefurbCommit_DefectProfit_Model

namespace RefurbCommit.DefectProfit

/-- Proposition 7 (p. B-1), with ᾱ (p. A-1) and v̄r (p. B-2): under commitment an optimal
price vector exists, and every optimal one sells no new units in period 2 and refurbishes
none / some / all of the defective returns according to ᾱ and v̄r. -/
theorem proposition_7 (P : Params) (hP : P.Standing)
    (hD : 0 < P.vr * (P.cn + P.h) - P.vn * (P.cr + P.h) * P.kr)
    (α : ℝ) (hα : 0 < α) (hpos : 0 < PiC P α) :
    (∃ p1 p2 pr, FeasibleC P α p1 p2 pr ∧ objC P α p1 p2 pr = PiC P α) ∧
    ∀ p1 p2 pr, FeasibleC P α p1 p2 pr → objC P α p1 p2 pr = PiC P α →
      q2C P α p1 p2 pr = 0 ∧
      -- i) no refurbishing
      (α ≤ alphaBar P → qrC P α p1 p2 pr = 0) ∧
      -- ii) refurbish some of the DPRs
      (alphaBar P < α → P.vr < vrBar P α →
        0 < qrC P α p1 p2 pr ∧ (1 + P.kr * α) * qrC P α p1 p2 pr < α * q1C P α p1 p2 pr) ∧
      -- iii) refurbish all of the DPRs
      (alphaBar P < α → vrBar P α ≤ P.vr →
        0 < qrC P α p1 p2 pr ∧ (1 + P.kr * α) * qrC P α p1 p2 pr = α * q1C P α p1 p2 pr) := by sorry

end RefurbCommit.DefectProfit
