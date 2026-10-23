-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_value_functions_well_defined
-- name    : StartupLaunch.Strategy.value_functions_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:42.980812+00:00
-- url     : https://prove2.me/theorems/407c0f75-188f-47e0-abf2-4c86efbe0d8d
-- title:
--   §4.1 and §4.2, (1)–(5), pp. 9–14 — the value functions Π_I and R_I are well defined
-- statement:
--   Assume the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$, and let $p \in [0,1]$ be the per-period success probability of the advanced product's development.
--
--   1. The established firm's equations (1)–(2),
--   $$\Pi_0 = \max\{\Pi_{LS},\Pi_{LC},\Pi_{DC}\},\qquad \Pi_1 = \max\{\Pi_{LS},\Pi_{LC}\},$$
--   have a solution $(\Pi_0,\Pi_1)$, and any two solutions coincide.
--   2. The startup's equations (3)–(5), imposed at every cash level $E$, have a solution $(R_0,R_1)$ for which $R_0(E) - E$ and $R_1(E) - E$ are bounded, and any two such solutions coincide.
--
--   The paper introduces $\Pi_I$ and $R_I$ as "the" expected profit and "the" value function; this statement is what makes those definite articles correct, and it guarantees that the statements of the mission, which quantify over all solutions, are not vacuous.
--
--   **Formalization Note.** This is not a numbered result of the paper. The launch-and-continue option of the startup is available only when $c \le E + v_o$, and the boundedness of $R_I(E) - E$ is the selection that singles out the value function (see the model definition).
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), p. 9 (PDF 10), §4.1, and p. 13 (PDF 14), §4.2, eqs. (1)–(5)

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem value_functions_well_defined (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∃ Pi0 Pi1 : ℝ, EstBellman P p Pi0 Pi1) ∧
    (∀ Pi0 Pi1 Pi0' Pi1' : ℝ, EstBellman P p Pi0 Pi1 → EstBellman P p Pi0' Pi1' →
      Pi0 = Pi0' ∧ Pi1 = Pi1') ∧
    (∃ R0 R1 : ℝ → ℝ, StartupBellman P p R0 R1) ∧
    (∀ R0 R1 R0' R1' : ℝ → ℝ, StartupBellman P p R0 R1 → StartupBellman P p R0' R1' →
      R0 = R0' ∧ R1 = R1') := by sorry

end StartupLaunch.Strategy
