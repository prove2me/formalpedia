-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_C_5_overlap_regime
-- name    : SpectralFeedback.Supplement.theorem_C_5_overlap_regime
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:57:34.386218+00:00
-- url     : https://prove2.me/theorems/38210444-acb3-42d1-aeb3-fb819ecdbc8d
-- title:
--   Theorem C.5 — the overlap regime $(m-1)r\le d\le mr$: closed form of $F_m(d,r)=G_{m,r}(I_d/d)$
-- statement:
--   Let $2\le r<d$ (standing in §C.5) and $F_m(d,r)=G_{m,r}(I_d/d)$, the value at the maximally mixed state. If $m\ge2$ and $(m-1)r\le d\le mr$, then
--
--   $$
--   F_m(d,r)=\frac{d-2m+1+\sqrt{(d-2m+1)^2+4m(m-1)(r-1)}}{2d}.\qquad\text{(C.17)}
--   $$
--
--   This value is strictly below the rank ceiling $(r-1)/r$ when $(m-1)r<d<mr$, and equals $(r-1)/r$ at both endpoints $d=(m-1)r$ and $d=mr$.
--
--   The formula interpolates between the disjoint-support regime $mr\le d$ and the saturated regime.
--
--   Differences from the source:
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: I_d/d → (d : ℂ)⁻¹ • 1 on ℂ^d; reason: same matrix
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem C.5, (C.17), p.30 (PDF p.32); standing assumptions §C.5, p.30

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem C.5** (The overlap regime; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.30 (PDF p.32)). With
`F_m(d, r) = G_{m,r}(I_d/d)` and the standing `2 ≤ r < d` of §C.5: if `m ≥ 2` and
`(m − 1)r ≤ d ≤ mr`, then
`F_m(d, r) = (d − 2m + 1 + √((d − 2m + 1)² + 4m(m − 1)(r − 1)))/(2d)` (C.17). It is strictly below
`(r − 1)/r` when `(m − 1)r < d < mr`, and equals that ceiling at both endpoints.

**Formalization Note** `I_d/d` is `(d : ℂ)⁻¹ • 1` on `ℂ^d`; `F_m(d, r) = v` is
`IsGreatest (rewardSet r (chi r) m (I_d/d)) v`. -/
theorem theorem_C_5_overlap_regime (m r d : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) (hrd : r < d)
    (h1 : (m - 1) * r ≤ d) (h2 : d ≤ m * r) :
    IsGreatest (rewardSet r (chi r) m (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ)))
        (((d : ℝ) - 2 * m + 1 +
          Real.sqrt (((d : ℝ) - 2 * m + 1) ^ 2 + 4 * m * ((m : ℝ) - 1) * ((r : ℝ) - 1))) / (2 * d)) ∧
      ((m - 1) * r < d → d < m * r →
        ((d : ℝ) - 2 * m + 1 +
          Real.sqrt (((d : ℝ) - 2 * m + 1) ^ 2 + 4 * m * ((m : ℝ) - 1) * ((r : ℝ) - 1))) / (2 * d) <
          ((r : ℝ) - 1) / r) ∧
      (d = (m - 1) * r ∨ d = m * r →
        ((d : ℝ) - 2 * m + 1 +
          Real.sqrt (((d : ℝ) - 2 * m + 1) ^ 2 + 4 * m * ((m : ℝ) - 1) * ((r : ℝ) - 1))) / (2 * d) =
          ((r : ℝ) - 1) / r) := by sorry

end Supplement

end SpectralFeedback
