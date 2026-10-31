-- Prove2me | Theorems.Thm_StartupLaunch_Strategy_lemma_1_ii_corrected
-- name    : StartupLaunch.Strategy.lemma_1_ii_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:01.750205+00:00
-- url     : https://prove2.me/theorems/fefc7f14-ec9f-43a7-b45a-6e8fdae64f89
-- title:
--   Lemma 1(ii) (corrected), p. 14 (PDF 15) — if p1 < p2 and p > p1, with funded development, launching and continuing strictly beats launching and stopping
-- statement:
--   Assume the standing assumptions $0 < v_o \le v_a$, $v_o < c$, $0 < \delta < 1$, $0 \le \alpha \le 1$, let $p \in [0,1]$, let $p_1 \le p_2$ be thresholds as in Proposition 1, and let $(R_0,R_1)$ be the startup's value functions. If $p_1 < p_2$ and $p > p_1$, then for every cash level $E$ with $c \le E + v_o$
--   $$R_{LC}(E) > R_{LS}(E).$$
--
--   Once development is likely enough to succeed and the period's development can be paid for, a startup that launches the on-hand product prefers to keep developing the advanced product.
--
--   **Formalization Note.** The printed Lemma 1(ii) reads "If $p \ge p_1$ and $c \le E + v_o$, $R_{LC}(E) > R_{LS}(E)$", which is false: with $v_o = 3/2$, $v_a = 5$, $c = 2$, $\delta = 9/10$, $\alpha = 3/5$ and $p = 1/5$ the thresholds are $p_1 = p_2 = 1/9$, yet $R_{LC}(1) = 14.9 < R_{LS}(1) = 16$. When $p_1 = p_2$ the established firm jumps directly from launch-and-stop to deferral, and the launch-and-continue option need not beat stopping. At $p = p_1$ the two options can tie. The statement here adds $p_1 < p_2$ and makes $p > p_1$ strict.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), p. 14 (PDF 15), Lemma 1(ii) (corrected)

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

namespace StartupLaunch.Strategy

theorem lemma_1_ii_corrected (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (h12 : p1 < p2) (hp : p1 < p) (E : ℝ) (hE : P.c ≤ E + P.vo) :
    RLS P E < RLC P p R1 E := by sorry

end StartupLaunch.Strategy
