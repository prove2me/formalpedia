-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_sec42_relEntropy_le_chiSq
-- name    : RobustDP.ChiSquare.sec42_relEntropy_le_chiSq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:52.561451+00:00
-- url     : https://prove2.me/theorems/a99b0b5e-4b5f-4302-a208-4ba82f9f8c33
-- title:
--   Section 4.2 — $D(p\|q)\le\sum_s (p(s)-q(s))^2/q(s)$
-- statement:
--   Let $\mathcal S$ be a finite set and $p,q\in\mathcal M(\mathcal S)$ probability measures with $q(s)>0$ for every $s$. With $D$ the relative entropy (natural logarithm, $0\log 0=0$),
--
--   $$
--   D(p\|q)=\sum_{s\in\mathcal S}p(s)\log\frac{p(s)}{q(s)}\ \le\ \sum_{s\in\mathcal S}p(s)\cdot\frac{p(s)-q(s)}{q(s)}\ =\ \sum_{s\in\mathcal S}\frac{(p(s)-q(s))^2}{q(s)} .
--   $$
--
--   Hence every $p$ in the χ² set (46) has $D(p\|q)\le t$: the χ² set is an inner, i.e. conservative, approximation of the relative-entropy confidence region (39).
--
--   **Formalization Note** The page justifies the inequality by "$\log(1+x)\le x$ for all $x\in\mathbf R$", which holds for $x>-1$; terms with $p(s)=0$ are $0$ on both sides. The middle sum is printed over "$s\in c\mathcal S$", a misprint for $s\in\mathcal S$. The statement is the two relations of the display; the equality uses $\sum_s p(s)=\sum_s q(s)=1$.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 18, Section 4.2, display before (46)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet
import Definitions.Def_RobustDP_ChiSquare_RelEntropy

namespace RobustDP.ChiSquare

/-- §4.2, the display before (46) (Iyengar, TR-2002-07, p. 18): for `p, q ∈ M(S)` with
`q(s) > 0`, `D(p‖q) ≤ ∑ p(s) (p(s) − q(s))/q(s) = ∑ (p(s) − q(s))²/q(s)`. -/
theorem sec42_relEntropy_le_chiSq {S : Type*} [Fintype S] (p q : S → ℝ)
    (hp : p ∈ stdSimplex ℝ S) (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) :
    relEntropy p q ≤ ∑ s, p s * ((p s - q s) / q s) ∧
      ∑ s, p s * ((p s - q s) / q s) = chiSqDist p q := by sorry

end RobustDP.ChiSquare
