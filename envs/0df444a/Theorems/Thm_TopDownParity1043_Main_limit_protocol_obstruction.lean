-- Prove2me | Theorems.Thm_TopDownParity1043_Main_limit_protocol_obstruction
-- name    : TopDownParity1043.Main.limit_protocol_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:33:25.070747+00:00
-- url     : https://prove2.me/theorems/43b0ed0c-d30d-408d-afbf-e9cd3d47499e
-- title:
--   Communication obstruction from the strong limit invariant
-- statement:
--   Let $X,Y$ be nonempty subsets of a finite Boolean cube, both with min-entropy deficit at most $k$. Let $t,m$ be nonnegative integers and let $p\in(0,1]$. Suppose $k\ge1$, $m\le k$, and the rectangle satisfies the $(p,k)$-limit condition on either side. If
--
--   $$(32768\cdot196^t k)^t p\le\frac12,$$
--
--   then no deterministic $t$-round protocol with at most $2^m$ messages at each node solves the coordinate-difference search problem on $X\times Y$.
--
--   The limit condition on the left means every point of $X$ is a $(p,k)$-limit of $Y$; on the right the roles are reversed. A point is a limit when its Bernoulli-$p$ subcube has at least $2^{|P|-k}$ points of the opposite set with probability at least $3/4$. This explicit finite parameter bound implements the communication invariant used to derive Theorem 3.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, proof sketches of Theorems 1 and 2 pp.7–8 and pp.12–13, combined with Lemma 10 and Theorem 3 pp.15–16. Explicit conservative constants 32768 and 196 instantiate the linear-deficit strong mirror argument.

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
import Definitions.Def_TopDownParity1043_Main_Limit
open TopDownParity1043.Main

theorem TopDownParity1043.Main.limit_protocol_obstruction (V : Type) [Fintype V] [DecidableEq V]
    (t m : ℕ) (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (hm : (m : ℝ) ≤ k) (hX : SetDeficitLE X k) (hY : SetDeficitLE Y k)
    (p : Bias) (hp : 0 < (p : ℝ))
    (hb : (32768*(196 : ℝ)^t*k)^t*(p : ℝ) ≤ 1/2)
    (hl : LeftLimit p k X Y ∨ RightLimit p k X Y) :
    ¬HasProtocol (X : Set (V → Bool)) (Y : Set (V → Bool)) t m  := by sorry
