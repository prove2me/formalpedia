-- Prove2me | Theorems.Thm_SilverRateSC_eq_11_29_constants
-- name    : SilverRateSC.eq_11_29_constants
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:07.894384+00:00
-- url     : https://prove2.me/theorems/d5b3b06f-f477-4789-ae4d-cb6babacd0a4
-- title:
--   (11) and §5.2 — $a_\beta\ge8$, $1<c_\beta<2$, $c_\beta=1+O(\beta)$, $\log a_\beta=O(1/\beta)$, $1/p(c_\beta)=1/p_{\rm sil}-O(\beta)$
-- statement:
--   For the explicit constants $c_\beta=\beta+\sqrt{1+2\beta}$ and $a_\beta=8+4\beta+4\exp[(\sqrt2R-\beta)/\beta]$, $R=1+\beta$, one has $a_\beta\ge8$ and $1<c_\beta<2$, and, uniformly for $0<\beta\le1/4$,
--   $$c_\beta=1+O(\beta),\qquad \log a_\beta=O(1/\beta),\qquad \frac1{p(c_\beta)}=\frac1{p_{\rm sil}}-O(\beta),$$
--   with $p_{\rm sil}=\log_2(1+\sqrt2)$.
--
--   These estimates drive the final choice $\beta=(\log\kappa)^{-1/2}$, which balances the loss $O(\beta\log\kappa)$ in the exponent against the loss $O(1/\beta)$ from $\log a_\beta$.
--
--   Differences from the source:
--   - encoding: X = Y + O(Z) uniformly when 0 < β ≤ 1/4 → ∃ C' > 0 before β with |X − Y| ≤ C' Z (|log a_β| ≤ C'/β for log a_β = O(1/β)); reason: standard meaning of a uniform O
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the paper pairs log with exp; another base changes only the constants
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), (11), p.15 and §5.2 'Choosing the Bending Parameter', p.24

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_aBeta

namespace SilverRateSC

/-- **The bending constants, (11) and the estimates before (29).** The construction yields
constants `a_β ≥ 8` and `1 < c_β < 2`, depending only on `β`, with `c_β = 1 + O(β)`,
`log a_β = O(1/β)`, uniformly when `0 < β ≤ 1/4` (11); moreover `1/p(c_β) = 1/p_sil − O(β)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, (11), p. 15, and §5.2 "Choosing the Bending Parameter", p. 24.

**Formalization Note** Each `O(·)` is written out with one constant `C'`, chosen before `β` (this is
"uniformly when `0 < β ≤ 1/4`"); `X = Y + O(Z)` reads `|X − Y| ≤ C' Z`. `a_β`, `c_β` are the
explicit constants (31), (34); `p_sil` is the published `SilverRateLB.pSil`; `log` is natural. -/
theorem eq_11_29_constants :
    ∃ C' : ℝ, 0 < C' ∧ ∀ β : ℝ, 0 < β → β ≤ 1 / 4 →
      8 ≤ aBeta β ∧ 1 < cBeta β ∧ cBeta β < 2 ∧
      |cBeta β - 1| ≤ C' * β ∧ |Real.log (aBeta β)| ≤ C' / β ∧
      |1 / pOf (cBeta β) - 1 / SilverRateLB.pSil| ≤ C' * β := by sorry

end SilverRateSC
