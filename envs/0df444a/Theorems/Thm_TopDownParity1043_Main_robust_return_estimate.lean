-- Prove2me | Theorems.Thm_TopDownParity1043_Main_robust_return_estimate
-- name    : TopDownParity1043.Main.robust_return_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:17:19.49503+00:00
-- url     : https://prove2.me/theorems/e566f072-3893-44e4-bd85-24b3ae627b25
-- title:
--   Robust return estimate with linear deficit dependence
-- statement:
--   Let $X$ be a nonempty subset of a finite Boolean cube with min-entropy deficit at most $k$, where $k\ge1$. Sample $x$ uniformly from $X$, and independently sample Bernoulli coordinate sets $P$ and $Q$ with biases $p$ and $q$. Put $s=p+q-pq$, and suppose a bias $r\in[0,1]$ satisfies $sr=p(1-q)$ and $r\le(32768k)^{-1}$. Then
--
--   $$\Pr_{x,P,Q}\left[\left|\left\{y\in[x]_P:|X\cap[y]_Q|<2^{|Q|-194k}\right\}\right|\le2^{|P|-k-6}\right]\ge\frac{31}{32}.$$
--
--   This is the robust counting estimate in the strong mirror-set argument, with Lemma 10 replacing the earlier light-pattern estimate. It provides the linear dependence on deficit needed for the exponent in Theorem 3. The larger return-deficit constant retains the loss from the new light-pattern threshold.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, canonical manuscript https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, pp.11–12 proof of Lemma 9, probability display (4), equations (5)–(6), combined with Lemma 10 and Section 4 pp.15–16. Constants adjusted to 32768=512*64 and 194 as required by the improved light-pattern threshold.

import Mathlib
import Definitions.Def_TopDownParity1043_Main_Limit
open TopDownParity1043.Main
open Classical

theorem TopDownParity1043.Main.robust_return_estimate (V : Type) [Fintype V] [DecidableEq V]
    (X : Finset (V → Bool)) (hX : X.Nonempty)
    (k : ℝ) (hk : 1 ≤ k) (hdef : setDeficit (Fintype.card V) X ≤ k)
    (p q s r : Bias) (hs : (s : ℝ) = (p : ℝ)+(q : ℝ)-(p : ℝ)*(q : ℝ))
    (hsr : (s : ℝ)*(r : ℝ) = (p : ℝ)*(1-(q : ℝ)))
    (hr : (r : ℝ) ≤ (32768*k)⁻¹) :
    (31 : ℝ)/32 ≤ (∑ x ∈ X, ∑ P : Finset V, setWeight p P *
      setProb q (fun Q =>
        ((Finset.univ.filter fun y : V → Bool => InSubcube x P y ∧
          ((fibre X y Q).card : ℝ) < (2 : ℝ)^((Q.card : ℝ)-194*k)).card : ℝ) ≤
            (2 : ℝ)^((P.card : ℝ)-k-6))) / X.card  := by sorry
