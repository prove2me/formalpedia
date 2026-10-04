-- Prove2me | Theorems.Thm_SunConj_chayote_Phi6_expansion
-- name    : SunConj.chayote_Phi6_expansion
-- status  : Open
-- author  : @williambc
-- created : 2026-10-04T01:04:34.535975+00:00
-- url     : https://prove2.me/theorems/efe22daf-ca00-455d-ad8d-351fe52aecf0
-- title:
--   Third-order expansion of the hypergeometric factor of Conjecture 5.6
-- statement:
--   # Third-order expansion of the hypergeometric factor of Conjecture 5.6
--
--   Lean: planned name `SunConj.chayote_Phi6_expansion`.
--
--   For real $x$ with $|x|<\frac18$ let
--   $$\Phi(x)=\sum_{j=0}^{\infty}\frac{(x)_j^2\,(2x)_j}{(\frac14+2x)_j\,(\frac34+2x)_j\,j!},$$
--   where $(c)_j=c(c+1)\cdots(c+j-1)$ is the rising factorial (Lean: `(ascPochhammer ℝ j).eval c`), the sum is Lean's real `tsum`, and for $|x|<\frac18$ no denominator vanishes (all $\frac14+2x+i,\frac34+2x+i>0$) and the series converges absolutely (`SunConj_conj5_6_shift_closed_form`, first conjunct).
--   Let $L_{-8}(2)=\sum_{n\ge1}\left(\frac{-8}{n}\right)n^{-2}$ (`LNeg8Two`, Kronecker symbol $\left(\frac{-8}{n}\right)=1,1,-1,-1,0$ for $n\equiv1,3,5,7$, even) and $\zeta(3)=\sum_{n\ge1}n^{-3}$ (`zeta3`). Then, for real $x\to0$,
--   $$\Phi(x)=1+\big(32\sqrt2\,\pi\,L_{-8}(2)-112\,\zeta(3)\big)\,x^3+O(x^4)$$
--   (Lean: `Asymptotics.IsBigO (nhds (0:ℝ)) (fun x => Φ x - (1 + (32 * √2 * π * LNeg8Two - 112 * zeta3) * x ^ 3)) (fun x => x ^ 4)`, with $\Phi$ written out as the `tsum` above; for $|x|\ge\frac18$ the `tsum` values are irrelevant to the big-O at $0$).
--
--   **Role.** With `SunConj_chayote_P6_expansion` and `SunConj_conj5_6_shift_closed_form` this gives `SunConj_chayote_S6_jet`. The $j=0$ term is $1$; for $j\ge1$ the term is $x^3$ times a function $r_j(x)$ with $r_j(0)=\frac{2\,((j-1)!)^3}{(\frac14)_j(\frac34)_j\,j!}=\frac{2\cdot64^j}{j^3\binom{2j}j\binom{4j}{2j}}$ and $|r_j(x)-r_j(0)|\le C|x|\,j^{-2}$ uniformly; the cubic coefficient is then $2\sum_{j\ge1}\frac{64^j}{j^3\binom{2j}j\binom{4j}{2j}}$, evaluated by `SunConj_conj5_6_tail_sum`.
--
--   **Source.** New here (chayote); this is the *Local expansion at 0* paragraph of `proofs/SunConj_conj5_6_first.md`, stated as a lemma.
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/a9c54f745fc614e8c91305e866a28985370aef9f/math-problems/statements/SunConj_chayote_Phi6_expansion.md

import Definitions.Def_SunConj_Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.Defs

open Filter Topology Asymptotics

namespace SunConj

theorem chayote_Phi6_expansion :
    (fun x : ℝ => (∑' j : ℕ, (ascPochhammer ℝ j).eval x ^ 2 * (ascPochhammer ℝ j).eval (2 * x) /
        ((ascPochhammer ℝ j).eval (1 / 4 + 2 * x) * (ascPochhammer ℝ j).eval (3 / 4 + 2 * x) *
          (Nat.factorial j : ℝ))) -
        (1 + (32 * Real.sqrt 2 * Real.pi * LNeg8Two - 112 * zeta3) * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => x ^ 4) := by sorry

end SunConj
