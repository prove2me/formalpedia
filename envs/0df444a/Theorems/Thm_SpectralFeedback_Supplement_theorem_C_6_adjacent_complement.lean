-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_C_6_adjacent_complement
-- name    : SpectralFeedback.Supplement.theorem_C_6_adjacent_complement
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:58:15.190902+00:00
-- url     : https://prove2.me/theorems/e98f113f-c725-45a9-8273-c151f444e214
-- title:
--   Theorem C.6 — the adjacent complement regime: $F_m(d,r)=\frac md\chi(a^{[s]},b^{[r-s]})$
-- statement:
--   Let $2\le r<d$ (standing in §C.5), $F_m(d,r)=G_{m,r}(I_d/d)$, $m\ge3$ and
--
--   $$
--   \frac{m(m-2)}{m-1}\,r\le d\le(m-1)r .
--   $$
--
--   Put $D=mr-d$ and $s=mr-(m-1)D$; then $0\le s\le r$. With $a=(m-1)/m$ and $b=(m-2)/(m-1)$,
--
--   $$
--   F_m(d,r)=\frac md\,\chi\bigl(a^{[s]},b^{[r-s]}\bigr),\qquad\text{(C.18)}
--   $$
--
--   where $x^{[j]}$ denotes $j$ repeated entries. Equivalently, $z=dF_m(d,r)$ is the positive root of
--
--   $$
--   z^2-\Bigl(d-2m+2+\frac1{m-1}\Bigr)z-m(m-2)(r-1)=0.\qquad\text{(C.19)}
--   $$
--
--   The value is strictly below the rank ceiling $(r-1)/r$ when $0<s<r$.
--
--   Differences from the source:
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: D, s and the repetition vector (a^[s], b^[r−s]) → D, s as integers; the vector with a at the 0-based indices i < s and b elsewhere; reason: same numbers
--   - encoding: z = dF_m(d, r) is the positive root of (C.19) → 0 < d·F and (d·F)² − (d − 2m + 2 + 1/(m − 1))(d·F) − m(m − 2)(r − 1) = 0; reason: the quadratic has a negative constant term, so it has exactly one positive root
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem C.6, (C.18)–(C.19), p.31 (PDF p.33); standing assumptions §C.5, p.30

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem C.6** (The adjacent complement regime; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.31 (PDF p.33)). With
`F_m(d, r) = G_{m,r}(I_d/d)` and the standing `2 ≤ r < d` of §C.5: let `m ≥ 3` and
`(m(m − 2)/(m − 1)) r ≤ d ≤ (m − 1)r`. Put `D = mr − d`, `s = mr − (m − 1)D`, so `0 ≤ s ≤ r`. Then,
with `a = (m − 1)/m` and `b = (m − 2)/(m − 1)`, `F_m(d, r) = (m/d) χ(a^{[s]}, b^{[r−s]})` (C.18).
Equivalently, `z = d F_m(d, r)` is the positive root of
`z² − (d − 2m + 2 + 1/(m − 1)) z − m(m − 2)(r − 1) = 0` (C.19). The value is strictly below the rank
ceiling `(r − 1)/r` when `0 < s < r`.

**Formalization Note** `D` and `s` are integers (`ℤ`); `x^{[j]}` is `j` repeated entries, so the
vector is `a` at the 0-based indices `i < s` and `b` at the others. `I_d/d` is `(d : ℂ)⁻¹ • 1`. The
local `s` is not a receiver rank. -/
theorem theorem_C_6_adjacent_complement (m r d : ℕ) (hm : 3 ≤ m) (hr : 2 ≤ r) (hrd : r < d)
    (h1 : (m : ℝ) * ((m : ℝ) - 2) / ((m : ℝ) - 1) * r ≤ d) (h2 : d ≤ (m - 1) * r) :
    let D : ℤ := (m : ℤ) * r - d
    let s : ℤ := (m : ℤ) * r - ((m : ℤ) - 1) * D
    let a : ℝ := ((m : ℝ) - 1) / m
    let b : ℝ := ((m : ℝ) - 2) / ((m : ℝ) - 1)
    let F : ℝ := (m : ℝ) / d * chi r (fun i => if ((i : ℕ) : ℤ) < s then a else b)
    0 ≤ s ∧ s ≤ r ∧
      IsGreatest (rewardSet r (chi r) m (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ))) F ∧
      (0 < (d : ℝ) * F ∧
        ((d : ℝ) * F) ^ 2 - ((d : ℝ) - 2 * m + 2 + 1 / ((m : ℝ) - 1)) * ((d : ℝ) * F) -
          m * ((m : ℝ) - 2) * ((r : ℝ) - 1) = 0) ∧
      (0 < s → s < r → F < ((r : ℝ) - 1) / r) := by sorry

end Supplement

end SpectralFeedback
