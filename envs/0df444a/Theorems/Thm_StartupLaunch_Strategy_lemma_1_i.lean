-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_lemma_1_i
-- name    : StartupLaunch.Strategy.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:57.878177+00:00
-- url     : https://prove2.me/theorems/1f3aef08-e9b0-40b6-8cd4-81376192d2b1
-- title:
--   Lemma 1(i), p. 14 (PDF 15) — if p < p1, launching and stopping strictly beats both continuing options at every cash level
-- statement:
--   Assume the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$, let $p \in [0,1]$, let $p_1 \le p_2$ be thresholds as in Proposition 1, and let $(R_0, R_1)$ be the startup's value functions (the solution of (3)–(5) with $R_I(E) - E$ bounded). If $p < p_1$, then for every cash level $E > 0$
--   $$R_{LS}(E) > \max\bigl[R_{DC}(E),\,R_{LC}(E)\bigr].$$
--
--   When development is unlikely to succeed, the startup behaves like the established firm: launching the on-hand product and abandoning the advanced product dominates, whatever its cash.
--
--   **Formalization Note.** $R_{LC}(E)$ denotes the formula of (4) evaluated even at cash levels where the option is unavailable ($c > E + v_o$); the inequality is claimed there as well.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), p. 14 (PDF 15), Lemma 1(i)

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem lemma_1_i (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (hp : p < p1) :
    ∀ E : ℝ, 0 < E → RDC P p R0 E < RLS P E ∧ RLC P p R1 E < RLS P E := by sorry

end StartupLaunch.Strategy
