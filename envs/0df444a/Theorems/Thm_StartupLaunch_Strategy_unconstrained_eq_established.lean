-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_unconstrained_eq_established
-- name    : StartupLaunch.Strategy.unconstrained_eq_established
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:02.059764+00:00
-- url     : https://prove2.me/theorems/6af72e0a-83cc-41b6-9f20-390337d35999
-- title:
--   Proof of Proposition 2(ii), Appendix p. 4 (PDF 42) — (corrected) above the interest break-even, the startup's value is its cash plus the established firm's value
-- statement:
--   Assume the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$, let $p \in [0,1]$, let $(R_0,R_1)$ be the startup's value functions and $(\Pi_0,\Pi_1)$ the established firm's values at the same $p$. Then
--   $$R_1(E) = E + \Pi_1 \quad\text{whenever } E \ge \frac{c - v_o}{1-\delta},\qquad R_0(E) = E + \Pi_0 \quad\text{whenever } E \ge \frac{c}{1-\delta}.$$
--
--   Above these levels the interest earned on the cash pays for development indefinitely, so the startup is no longer cash constrained and acts exactly as the established firm, holding its cash on the side. This is the precise content of the limit comparison the paper uses in the proof of Proposition 2(ii).
--
--   **Formalization Note.** The proof prints $\lim_{E\to\infty} R_{LC} = \Pi_{LC}$ and $\lim_{E\to\infty} R_{DC} = \Pi_{DC}$; both sides of these limits are not comparable as written, since $R_{LC}(E)$ and $R_{DC}(E)$ grow like $E$. The exact identity above, with explicit cash levels, is the corrected statement.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), Appendix p. 4 (PDF 42), proof of Proposition 2(ii) (corrected)

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem unconstrained_eq_established (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1) (Pi0 Pi1 : ℝ)
    (hPi : EstBellman P p Pi0 Pi1) :
    (∀ E : ℝ, (P.c - P.vo) / (1 - P.δ) ≤ E → R1 E = E + Pi1) ∧
    (∀ E : ℝ, P.c / (1 - P.δ) ≤ E → R0 E = E + Pi0) := by sorry

end StartupLaunch.Strategy
