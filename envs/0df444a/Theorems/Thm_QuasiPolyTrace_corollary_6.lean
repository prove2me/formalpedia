-- Prove2me | Theorems.Thm_QuasiPolyTrace_corollary_6
-- name    : QuasiPolyTrace.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:48.615916+00:00
-- url     : https://prove2.me/theorems/262ee4b4-7669-4634-802a-4a350558b58f
-- title:
--   Corollary 6 — zooming out is a binomial mixture of shifted statistics
-- statement:
--   Let $x\in\{0,1\}^n$, let $p\in[0,1]$, let $s$ be a nonempty statistic (a finite set of positions) and let $0\le R\le n$. Then
--
--   $$
--   x^{(s)}_{[1:n],p}=\varepsilon+\sum_{j=0}^{R}\mathrm{bin}(R,j,p)\,x^{(s-j)}_{[R+1:n],p}
--   \qquad\text{with}\qquad 0\le\varepsilon\le \Pr\big[\mathrm{Bin}(R,p)\ge \min_i s_i\big].
--   $$
--
--   Here $x_{[R+1:n]}$ is $x$ with its first $R$ bits removed, $s-j$ is the statistic shifted by $-j$ (reading $0$ when an entry falls below $1$), and $\Pr[\mathrm{Bin}(R,p)\ge m]=\sum_{j=0}^{R}\mathrm{bin}(R,j,p)\,[j\ge m]$.
--
--   Zooming out from a substring to the whole string blurs each statistic by a binomial shift, up to a small tail error; Proposition 37 applies this twice in each induction step.
--
--   Differences from the source:
--   - reading: p a probability (Definition 1, implicit) → 0 ≤ p ≤ 1; reason: the corollary is about the deletion channel, whose parameter is a probability
--   - encoding: a statistic s, a tuple of positions with min_i s_i → a nonempty finite set of integers; s − j is shift s (−j); reason: tuples have distinct entries and bits are 0/1, so a set changes no value; nonempty so that min_i s_i exists
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Corollary 6, p.7

import Mathlib
import Definitions.Def_QuasiPolyTrace_bin
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_shift

namespace QuasiPolyTrace

/-- **Corollary 6 (zooming out is a binomial mixture of shifted statistics).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Corollary 6, p.7:
"Let x ∈ {0,1}^n. For any statistic s and 0 ≤ R ≤ n, we have
`x^{(s)}_{[1:n]} = ε + ∑_{j=0}^{R} bin(R, j, p) · x^{(s−j)}_{[R+1:n]}` where
`0 ≤ ε ≤ Pr[Bin(R, p) ≥ min_i s_i]`."

**Formalization Note.**
* `x^{(s)}_{[1:n]}` is `stat p x s`, and `x_{[R+1:n]}` is `x.drop R`.
* `p ∈ [0, 1]` is the paper's standing "probability p" (Definition 1).
* The statistic is a nonempty finite set of integers (so that `min_i s_i` exists); a shifted statistic with
  an entry `≤ 0` reads 0, as the paper notes after the corollary (p.7).
* `Pr[Bin(R, p) ≥ m] = ∑_{j=0}^{R} bin(R, j, p) [j ≥ m]`. -/
theorem corollary_6 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : List Bool) (s : Finset ℤ)
    (hs : s.Nonempty) (R : ℕ) (hR : R ≤ x.length) :
    ∃ ε : ℝ, stat p x s = ε + ∑ j ∈ Finset.range (R + 1), bin R j p * stat p (x.drop R) (shift s (-(j : ℤ))) ∧
      0 ≤ ε ∧ ε ≤ ∑ j ∈ Finset.range (R + 1), (if s.min' hs ≤ (j : ℤ) then bin R j p else 0) := by sorry

end QuasiPolyTrace
