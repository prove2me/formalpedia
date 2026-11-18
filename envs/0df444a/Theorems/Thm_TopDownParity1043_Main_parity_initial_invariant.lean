-- Prove2me | Theorems.Thm_TopDownParity1043_Main_parity_initial_invariant
-- name    : TopDownParity1043.Main.parity_initial_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:38:30.00431+00:00
-- url     : https://prove2.me/theorems/9944f12b-2271-47d9-b1f5-65492ac6ba1e
-- title:
--   Parity initializes the limit invariant on both sides
-- statement:
--   Let $n\ge1$ and let $p\in[0,1]$ satisfy $np\ge2$. Let $X$ be the even-parity words in $\{0,1\}^n$ and $Y$ the odd-parity words. Then both sets are nonempty with deficit at most one, and
--
--   $$X\times Y\text{ satisfies the }(p,1)\text{-limit condition on both sides.}$$
--
--   Thus every point on either side has, with probability at least $3/4$ over a Bernoulli-$p$ coordinate set $P$, at least $2^{|P|-1}$ points of the opposite side in its subcube. This initializes the communication invariant; in particular the source chooses $p=2/n$.
-- source:
--   Oliver Korten, Top-Down Lower Bounds for All Depths, STOC 2027 submission 1043, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1043.pdf, proof sketches of Theorems 1 and 2, pp.7–8 and p.12: the initial parity rectangle satisfies the condition on both sides, with p0=p1=2/n; and Section 3 definition of the (p,k)-limit condition, p.10.

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW
import Definitions.Def_TopDownParity1043_Main_Limit
open TopDownParity1043.Main

theorem TopDownParity1043.Main.parity_initial_invariant (n : ℕ) (hn : 0 < n) (p : Bias)
    (hp : 2 ≤ (n : ℝ)*(p : ℝ)) :
    SetDeficitLE (Finset.univ.filter fun x : Fin n → Bool => parity n x = false) 1 ∧
    SetDeficitLE (Finset.univ.filter fun x : Fin n → Bool => parity n x = true) 1 ∧
    LeftLimit p 1 (Finset.univ.filter fun x : Fin n → Bool => parity n x = false)
      (Finset.univ.filter fun x : Fin n → Bool => parity n x = true) ∧
    RightLimit p 1 (Finset.univ.filter fun x : Fin n → Bool => parity n x = false)
      (Finset.univ.filter fun x : Fin n → Bool => parity n x = true)  := by sorry
