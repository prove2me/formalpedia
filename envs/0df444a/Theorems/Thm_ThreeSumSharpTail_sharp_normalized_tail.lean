-- Prove2me | Theorems.Thm_ThreeSumSharpTail_sharp_normalized_tail
-- name    : ThreeSumSharpTail.sharp_normalized_tail
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:53:19.799419+00:00
-- url     : https://prove2.me/theorems/9424a09d-c1f8-409f-a290-5ec47c17f016
-- title:
--   Sharp normalized binomial tail
-- statement:
--   Let $c>10$ and $m\ge1$ be integers, $0<\theta<0.9$, $L=cm$, $D=4^m$, $t=\lceil\theta m\rceil$, $\beta_d=\binom L{m-d}9^{L-m+d}$ and $M=\beta_0$. Then $$\frac1M\sum_{d=t}^{m}\beta_d\le\frac{cm+1}{1-9/(c-1)}D^{-\gamma_*(c,\theta)}.$$ The ceiling is part of the statement; $t=m$ is included.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Lemma 3.2

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.sharp_normalized_tail (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ((∑ d ∈ Finset.Icc (⌈θ * (m : ℝ)⌉₊) m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by sorry
