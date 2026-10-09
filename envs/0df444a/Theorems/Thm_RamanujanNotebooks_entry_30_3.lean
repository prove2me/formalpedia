-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_30_3
-- name    : RamanujanNotebooks.entry_30_3
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T21:57:28.063979+00:00
-- url     : https://prove2.me/theorems/5dabef4a-e8c3-43ac-9011-3bed07737f44
-- title:
--   Partial fractions of π²/(sin²(πz)(e^{2πz}−1))
-- statement:
--   Let $z\in\mathbb C$ with $z\notin\mathbb Z$ and $z\notin i\mathbb Z$. Then $$\frac{\pi^2}{\sin^2(\pi z)(e^{2\pi z}-1)}=\frac1{2\pi z^3}-\frac1{2z^2}+\frac{\pi}{3z}-\sum_{n\ge1}\frac1{(z+n)^2}+4z\sum_{n\ge1}\frac{n}{(e^{2\pi n}-1)(z^2-n^2)^2}-2\pi z^3\sum_{n\ge1}\frac1{\sinh^2(\pi n)(z^4-n^4)},$$ all three series converging absolutely. Differs from the printed source: the book states no condition on $z$; the exclusion of the poles $z\in\mathbb Z\cup i\mathbb Z$ is added by us.
--
--   **Discrepancy from the printed source.** Differs from the printed source: the book (p. 359) writes 'We have' with no condition on z. We add z ∉ ℤ and z ∉ iℤ, exactly the poles of the left side (where terms on the right are undefined too). Added by us; no change to the formula. The Codex audit (AUDIT_codex.md) re-read the page, confirmed formula and exclusions at 50 digits (residual below 7e-50 at its three points) and asked for relation domain_strengthened.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 30, Entry 3, p. 359, eq. (3.1).

import Mathlib

namespace RamanujanNotebooks
theorem entry_30_3 (z : ℂ)
    (hz : ∀ n : ℤ, z ≠ (n : ℂ))
    (hz' : ∀ n : ℤ, z ≠ (n : ℂ) * Complex.I) :
    ∃ S₁ S₂ S₃ : ℂ,
      HasSum (fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2) S₁ ∧
      HasSum (fun n : ℕ => ((n : ℂ) + 1) /
        ((Complex.exp (2 * (Real.pi : ℂ) * ((n : ℂ) + 1)) - 1) *
          (z ^ 2 - ((n : ℂ) + 1) ^ 2) ^ 2)) S₂ ∧
      HasSum (fun n : ℕ => 1 /
        (Complex.sinh ((Real.pi : ℂ) * ((n : ℂ) + 1)) ^ 2 *
          (z ^ 4 - ((n : ℂ) + 1) ^ 4))) S₃ ∧
      (Real.pi : ℂ) ^ 2 /
          (Complex.sin ((Real.pi : ℂ) * z) ^ 2 *
            (Complex.exp (2 * (Real.pi : ℂ) * z) - 1)) =
        1 / (2 * (Real.pi : ℂ) * z ^ 3) - 1 / (2 * z ^ 2) + (Real.pi : ℂ) / (3 * z)
          - S₁ + 4 * z * S₂ - 2 * (Real.pi : ℂ) * z ^ 3 * S₃ := by sorry
end RamanujanNotebooks
