-- Prove2me | Theorems.Thm_PathORAMCap_proposition_4_4
-- name    : PathORAMCap.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:52.250044+00:00
-- url     : https://prove2.me/theorems/489f6b92-77c7-4f72-ac8e-65cc06649d19
-- title:
--   Proposition 4.4 — $\mathbb E[(7/5)^{Q_h}]\le 23/20$ for every height $h$
-- statement:
--   Let $\mathbb P[G=k]=2^{-k-1}$ for $k\ge0$, $Q_0=0$, and for $h\ge0$
--
--   $$Q_{h+1}\overset d=\bigl(G+Q^{(0)}_h+Q^{(1)}_h-4\bigr)^+,$$
--
--   where $Q^{(0)}_h,Q^{(1)}_h$ are independent copies of $Q_h$, independent of $G$. Then for every integer $h\ge0$
--
--   $$\mathbb E\bigl[(7/5)^{Q_h}\bigr]\le\frac{23}{20}.$$
--
--   The bound is uniform in the height, which is what makes the stash bound uniform in the database size.
--
--   Differences from the source:
--
--   - encoding: Q_h, the root overflow of an independent geometric-load tree of height h (Definition 4.2) → QLaw Z h : PMF ℕ, defined by the law recursion (16)/(48) from Q_0 = 0; reason: the recursion, stated in the paper, determines the law uniquely; every statement involves Q_h only through its law
--   - encoding: moments and means of Q_h as real numbers → tsums in ℝ≥0∞; reason: they may be infinite in general, and ℝ≥0∞ needs no summability side condition; the stated bounds are finite values
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Proposition 4.4, p.15 (PDF p.18), eq. (18)

import Mathlib
import Definitions.Def_PathORAMCap_QLaw

set_option autoImplicit false

namespace PathORAMCap

/-- **Proposition 4.4** (Uniform Geometric Moment Bound; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.15 (PDF p.18)): "Let G be a random
variable with P[G = k] = 2−k−1 for integers k ≥ 0. Set Q0 = 0 and, for every integer h ≥ 0, define
Qh+1 =d (G + Q(0)h + Q(1)h − 4)+, where x+ = max{x, 0}, and Q(0)h and Q(1)h are independent copies of
Qh that are also independent of G. Then, for every integer h ≥ 0, E[(7/5)^Qh] ≤ 23/20. (18)"

**Formalization Note.** `Q_h` is given by its law `QLaw 4 h`, defined by this recursion; the moment is
in `ℝ≥0∞`. -/
theorem proposition_4_4 (h : ℕ) : QMoment 4 h (7 / 5) ≤ ENNReal.ofReal (23 / 20) := by sorry

end PathORAMCap
