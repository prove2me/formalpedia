-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_lower_bound_identity_sec_4_3
-- name    : SoSLinAlg.WeakRank.lower_bound_identity_sec_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:30:49.566697+00:00
-- url     : https://prove2.me/theorems/842e1ecc-aaa7-432d-9455-3875b5868625
-- title:
--   §4.3 — lower bound for the identity instance
-- statement:
--   Let $n>r\ge1$ be integers. In the real polynomial ring of two independent $n\times r$ matrices of indeterminates, consider $\operatorname{WRank}_r^n(I_n)$, the equations $XY^\top=I_n$. For every nonnegative integer $D$,
--   $$D\le2r+1\quad\Longrightarrow\quad\neg\bigl(\vdash_D\operatorname{WRank}_r^n(I_n)\bigr).$$
--   The notation $\vdash_D$ denotes a sum-of-squares refutation with each product and the sum-of-squares polynomial of degree at most $D$.
--
--   This is the identity-instance lower bound used with Proposition 1.10. Odd degrees and the boundary degrees zero and one remain included; the variables have no Boolean axioms or norm bounds.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity → totalDegree 0 = 0 at nonnegative upper bounds; reason: all bounds in this item are nonnegative, so the allowed polynomials are unchanged
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, §4.3 Lower Bound, PDF p.17 (printed p.15); proof PDF pp.17–19 (printed pp.15–17)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank

namespace SoSLinAlg.WeakRank

/-- §4.3, PDF pp.17–19 (printed pp.15–17): all natural degrees up to 2r+1. -/
theorem lower_bound_identity_sec_4_3 {n r : ℕ} (hr : 0 < r) (hrn : r < n) :
    ∀ D : ℕ, D ≤ 2 * r + 1 →
      ¬ SoSRefutable (WRank r (1 : Matrix (Fin n) (Fin n) ℝ)) D := by sorry

end SoSLinAlg.WeakRank
