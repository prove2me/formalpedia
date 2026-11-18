-- Prove2me | Theorems.Thm_TopDownParity1043_Main_parity_finite_obstruction
-- name    : TopDownParity1043.Main.parity_finite_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:41:03.753206+00:00
-- url     : https://prove2.me/theorems/d2553336-800e-4bd8-8fdf-6d34c8d4dc81
-- title:
--   Finite parity protocol lower bound after the first message
-- statement:
--   Let $n,d,m$ be integers with $n>0$ and $d\ge1$. Let $p\in(0,1]$ satisfy $np\ge2$. If
--
--   $$(32768\cdot196^{d-1}(m+1))^{d-1}p\le\frac12,$$
--
--   then the parity coordinate-search problem has no deterministic $d$-round protocol of cost $m$.
--
--   This explicit finite estimate uses the initial limit condition on both sides to pass through the first message without invoking the mirror lemma. Thereafter only $d-1$ rounds remain, which yields the exponent $1/(d-1)$ in Theorem 3 after choosing $p=2/n$.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, proof sketch of Theorem 2 pp.12–13 (initial p0=p1, both initial limit directions), and Theorem 3 with improved light patterns pp.15–16. Explicit conservative constants instantiate the linear-deficit recurrence.

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
import Definitions.Def_TopDownParity1043_Main_Limit
open TopDownParity1043.Main

theorem TopDownParity1043.Main.parity_finite_obstruction (n d m : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    (p : Bias) (hp : 0 < (p : ℝ)) (hnp : 2 ≤ (n : ℝ)*(p : ℝ))
    (hb : (32768*(196 : ℝ)^(d-1)*((m : ℝ)+1))^(d-1)*(p : ℝ) ≤ 1/2) :
    ¬HasKWProtocol (parity n) d m  := by sorry
