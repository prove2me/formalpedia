-- Prove2me | Theorems.Thm_PathORAMCap_lemma_5_5
-- name    : PathORAMCap.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:43.819908+00:00
-- url     : https://prove2.me/theorems/788d1e43-edfa-4770-9e76-b19b95a25065
-- title:
--   Lemma 5.5 — $\mathbb E[\min\{32,Q^{(3)}_{14}\}]>11/2$
-- statement:
--   For a capacity-three independent geometric-load tree with fourteen bucket levels,
--
--   $$\mathbb E\bigl[\min\{32,Q^{(3)}_{14}\}\bigr]>\frac{11}{2},$$
--
--   where $Q^{(3)}_h$ is the root overflow with capacity three: $Q^{(3)}_0=0$, $Q^{(3)}_{h+1}\overset d=(G+Q^{(3)}_{h,0}+Q^{(3)}_{h,1}-3)^+$. This finite surplus is what the transfer of Lemma 5.4 carries to a real scan region.
--
--   Differences from the source:
--
--   - encoding: Q_h, the root overflow of an independent geometric-load tree of height h (Definition 4.2) → QLaw Z h : PMF ℕ, defined by the law recursion (16)/(48) from Q_0 = 0; reason: the recursion, stated in the paper, determines the law uniquely; every statement involves Q_h only through its law
--   - encoding: moments and means of Q_h as real numbers → tsums in ℝ≥0∞; reason: they may be infinite in general, and ℝ≥0∞ needs no summability side condition; the stated bounds are finite values
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 5.5, p.40 (PDF p.43), eq. (50); (48), p.40

import Mathlib
import Definitions.Def_PathORAMCap_QLaw

set_option autoImplicit false

namespace PathORAMCap

/-- **Lemma 5.5** (Finite Local Surplus; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.40 (PDF p.43)): "For a capacity-three geometric tree
with fourteen bucket levels, E[min{32, Q(3)14}] > 11/2. (50)"

**Formalization Note.** `Q^(3)_14` is given by its law `QLaw 3 14` ((48)); the capped mean is in
`ℝ≥0∞`. -/
theorem lemma_5_5 : ENNReal.ofReal (11 / 2) < QCapMean 3 14 32 := by sorry

end PathORAMCap
