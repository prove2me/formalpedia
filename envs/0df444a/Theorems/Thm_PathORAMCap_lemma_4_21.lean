-- Prove2me | Theorems.Thm_PathORAMCap_lemma_4_21
-- name    : PathORAMCap.lemma_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:24.555205+00:00
-- url     : https://prove2.me/theorems/a32b2151-64e8-42d2-9046-c5f328510f9d
-- title:
--   Lemma 4.21 — $M_{12}<111/100<r$, $B_{12}<b$, $ar^2+b<r$ for $r=23/20$, $b=57621/100000$
-- statement:
--   For the recursion $Q_0=0$, $Q_{h+1}\overset d=(G+Q^{(0)}_h+Q^{(1)}_h-4)^+$, with $u=7/5$, $M_h=\mathbb E[u^{Q_h}]$, $a=1/(u^4(2-u))$, $c(k)=\sum_{g\ge0}2^{-g-1}(1-u^{g+k-4})^+$ and $B_h=\mathbb E[c(Q^{(0)}_h+Q^{(1)}_h)]$, the three conditions of Lemma 4.20 hold with $H=12$, $r=23/20$, $b=57621/100000$. More precisely,
--
--   $$M_{12}<\tfrac{111}{100}<r,\qquad B_{12}<b,\qquad ar^2+b<r.$$
--
--   With the monotonicity of $M_h$ and $B_h$ and the recurrence $M_{h+1}=aM_h^2+B_h$, these finite-height inequalities give the all-height bound of Proposition 4.4.
--
--   Differences from the source:
--
--   - encoding: Q_h, the root overflow of an independent geometric-load tree of height h (Definition 4.2) → QLaw Z h : PMF ℕ, defined by the law recursion (16)/(48) from Q_0 = 0; reason: the recursion, stated in the paper, determines the law uniquely; every statement involves Q_h only through its law
--   - encoding: moments and means of Q_h as real numbers → tsums in ℝ≥0∞; reason: they may be infinite in general, and ℝ≥0∞ needs no summability side condition; the stated bounds are finite values
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 4.21, p.33 (PDF p.36), eq. (34); notation (32), p.31 (PDF p.34)

import Mathlib
import Definitions.Def_PathORAMCap_QLaw

set_option autoImplicit false

namespace PathORAMCap

/-- **Lemma 4.21** (Verification of the Three Conditions at h = 12; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.33 (PDF p.36)): "For the
recursion Q0 = 0, Qh+1 =d (G + Q(0)h + Q(1)h − 4)+, h ≥ 0, all three conditions of Lemma 4.20 hold
with H = 12, r = 23/20, b = 57621/100000. More precisely, M12 < 111/100 < r, B12 < b, ar² + b < r. (34)"

**Formalization Note.** With `u = 7/5` (p.31): `M_h = E[u^{Q_h}]` (`QMoment 4 h (7/5)`, in `ℝ≥0∞`),
`a = 1/(u⁴(2 − u))` (`aConst`), `c(k) = Σ_g 2^{−g−1}(1 − u^{g+k−4})⁺` and
`B_h = E[c(Q^(0)_h + Q^(1)_h)]` (`BFun`, in `ℝ≥0∞`), as in (32). The four strict inequalities of
(34) are the four conjuncts. -/
theorem lemma_4_21 :
    QMoment 4 12 (7 / 5) < ENNReal.ofReal (111 / 100) ∧ (111 / 100 : ℝ) < 23 / 20 ∧
      BFun 12 < ENNReal.ofReal (57621 / 100000) ∧
      aConst * (23 / 20) ^ 2 + 57621 / 100000 < (23 / 20 : ℝ) := by sorry

end PathORAMCap
