-- Prove2me | Theorems.Thm_PolyContract_theorem_3_6
-- name    : PolyContract.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:51:46.220306+00:00
-- url     : https://prove2.me/theorems/4b7173b2-3936-4f17-bfb7-4e9e86247d7f
-- title:
--   Theorem 3.6 — breakpoints and an optimal contract have $O(n\nu)$ bits
-- statement:
--   Let $(f,m,\beta)$ be a valid instance with quadratic costs on $n$ elements. Suppose that every $m_e$, every $\beta_e$ and every value $f(S)$ is a quotient of two integers of absolute value less than $2^\nu$, and $n\le\nu$. Then every breakpoint of $x^\star$ and some optimal contract are rationals whose numerators and denominators have bit length $O(n\nu)$.
--
--   This bounds the size of the certificate in the membership half of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: bit length O(nν) → one absolute constant C, chosen before the instance, with numerator and denominator below 2^{C·n·ν}; reason: standard reading of O(·)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.6, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance
import Definitions.Def_PolyContract_BitLength

set_option autoImplicit false

namespace PolyContract

/-- **Theorem 3.6** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, p.8). "Suppose that every `m_e`, every `β_e`, and every value `f(S)` is a
quotient of two integers of absolute value less than `2^ν`, and `n ≤ ν`. Then every breakpoint
of `x⋆` and some optimal contract are rationals whose numerators and denominators have bit length
`O(nν)`."

**Formalization Note** Valid instances with quadratic costs on `n = |E|` elements. `O(nν)` reads:
one absolute constant `C`, chosen before the instance, bounds the bit lengths by `C·n·ν`. -/
theorem theorem_3_6 :
    ∃ C : ℕ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : QuadInstance ι) (ν : ℕ),
      I.Valid → (∀ e, IsSmallQuot ν (I.m e)) → (∀ e, IsSmallQuot ν (I.β e)) →
      (∀ S, IsSmallQuot ν (I.f S)) → Fintype.card ι ≤ ν →
      (∀ b : ℝ, I.IsBreakpoint b → HasBitLength (C * Fintype.card ι * ν) b) ∧
      ∃ a : ℝ, I.IsOptimalContract a ∧ HasBitLength (C * Fintype.card ι * ν) a := by sorry

end PolyContract
