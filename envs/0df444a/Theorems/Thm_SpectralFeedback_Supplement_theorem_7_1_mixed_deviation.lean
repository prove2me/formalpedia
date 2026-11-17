-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_7_1_mixed_deviation
-- name    : SpectralFeedback.Supplement.theorem_7_1_mixed_deviation
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:56:03.703979+00:00
-- url     : https://prove2.me/theorems/75c15872-5e6c-4302-9450-8c21fb654964
-- title:
--   Theorem 7.1 — mixed spectral deviation: $G_{m,s}(\rho)=\chi_s(mb+a-c,mb,\dots,mb)$
-- statement:
--   Let $m,s\ge2$ and $p=ms$, and let $\rho\succeq0$ be a complex $d\times d$ matrix whose leading $p$ eigenvalues (decreasing, padded with zeros, not renormalized) are
--
--   $$
--   (b+a,\ \underbrace{b,\dots,b}_{p-2},\ b-c),\qquad a\ge0,\quad 0\le c\le b.
--   $$
--
--   Then the $m$-symbol value with receiver rank $s$ is
--
--   $$
--   G_{m,s}(\rho)=\chi_s(mb+a-c,\ mb,\ \dots,\ mb),
--   $$
--
--   with $s-1$ entries $mb$ (7.1). Writing $x=mb+a-c$ and $y=mb$, this equals
--
--   $$
--   \frac{(s-2)y+\sqrt{(s-2)^2y^2+4(s-1)xy}}{2}.\qquad (7.2)
--   $$
--
--   So a spike $a$ and a dip $c$ enter the value only through their difference $a-c$.
--
--   Differences from the source:
--   - generalization: ρ the trace-one acquisition Gram of the main text → any positive semidefinite ρ (any trace); reason: the appendix form (Theorem G.5, §G.1.1) defines G_{m,s} for subnormalized matrices; at tr ρ = 1 it is the source's statement
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: the (unnormalized) active spectrum λ_1, …, λ_p, zero-padded → eigDesc ρ i for i < p (0-based); reason: the published eigDesc pads with zeros beyond d; same numbers
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem 7.1, (7.1)–(7.2), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem 7.1** (A mixed spectral deviation; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.12 (PDF p.14)). Let `p = ms`
and `m, s ≥ 2`. If the unnormalized active spectrum is `(b + a, b^{[p−2]}, b − c)` with `a ≥ 0` and
`0 ≤ c ≤ b`, then `G_{m,s}(ρ) = χ_s(mb + a − c, mb, …, mb)` (7.1). Writing `x = mb + a − c` and
`y = mb`, this equals `((s − 2)y + √((s − 2)²y² + 4(s − 1)xy))/2` (7.2).

**Formalization Note** `G_{m,s}(ρ) = v` is `IsGreatest (rewardSet s (chi s) m ρ) v` (the published
reward set with `F = χ_s`). The active spectrum is the leading `p` eigenvalues of `ρ`, decreasing and
zero-padded (`eigDesc ρ i`, `i < p`, 0-based), not renormalized; `p ≤ d` is not assumed. `ρ` is any
complex positive semidefinite `d × d` matrix (the main text's `ρ` has trace one; the appendix form,
Theorem G.5, allows any positive `ρ`). -/
theorem theorem_7_1_mixed_deviation (m s : ℕ) (hm : 2 ≤ m) (hs : 2 ≤ s) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcb : c ≤ b)
    (hspec : eigDesc ρ 0 = b + a ∧ (∀ i, 1 ≤ i → i ≤ m * s - 2 → eigDesc ρ i = b) ∧
      eigDesc ρ (m * s - 1) = b - c) :
    IsGreatest (rewardSet s (chi s) m ρ)
        (chi s (fun i => if (i : ℕ) = 0 then (m : ℝ) * b + a - c else (m : ℝ) * b)) ∧
      chi s (fun i => if (i : ℕ) = 0 then (m : ℝ) * b + a - c else (m : ℝ) * b) =
        (((s : ℝ) - 2) * ((m : ℝ) * b) +
          Real.sqrt (((s : ℝ) - 2) ^ 2 * ((m : ℝ) * b) ^ 2 +
            4 * ((s : ℝ) - 1) * ((m : ℝ) * b + a - c) * ((m : ℝ) * b))) / 2 := by sorry

end Supplement

end SpectralFeedback
