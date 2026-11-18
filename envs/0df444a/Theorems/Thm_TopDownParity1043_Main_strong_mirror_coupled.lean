-- Prove2me | Theorems.Thm_TopDownParity1043_Main_strong_mirror_coupled
-- name    : TopDownParity1043.Main.strong_mirror_coupled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:25:28.16342+00:00
-- url     : https://prove2.me/theorems/c0e51e71-63d9-4b5a-b91b-d837e6e41d30
-- title:
--   Strong mirror set from the improved light-pattern estimate
-- statement:
--   Let $X,Y$ be subsets of a finite Boolean cube. Suppose $X$ is nonempty with min-entropy deficit at most $k$, where $k\ge1$, and every $x\in X$ is a $(p,k)$-limit of $Y$. Let $p,q,s,r\in[0,1]$ satisfy $s=p+q-pq$, $sr=p(1-q)$, and $r\le(32768k)^{-1}$. There exists a subset $Y'\subseteq Y$ such that
--
--   $$D_\infty(Y')\le2k+2,\qquad \forall y\in Y',\quad y\text{ is a }(q,194k)\text{-limit of }X.$$
--
--   Here a $(p,k)$-limit means that a Bernoulli-$p$ subcube based at the point contains at least $2^{|P|-k}$ points of the set with probability at least $3/4$. The deficit bound includes nonemptiness. This strong mirror-set statement switches the direction of the communication invariant with linear dependence on the deficit. Its explicit coupling parameters describe the conditional difference law used in the source.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, canonical manuscript https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, Lemma 9 and proof pp.10–12, with Lemma 10 and Section 4 pp.15–16. Return-deficit multiplier adjusted to 194 to retain the new threshold loss; conditional bias r expressed through s=p+q-pq and sr=p(1-q).

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Limit
open TopDownParity1043.Main

theorem TopDownParity1043.Main.strong_mirror_coupled (V : Type) [Fintype V] [DecidableEq V]
    (X Y : Finset (V → Bool)) (k : ℝ) (hk : 1 ≤ k)
    (p q s r : Bias)
    (hX : SetDeficitLE X k) (hlimit : LeftLimit p k X Y)
    (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    ∃ Y' : Finset (V → Bool), Y' ⊆ Y ∧ SetDeficitLE Y' (2*k+2) ∧
      RightLimit q (194*k) X Y'  := by sorry
