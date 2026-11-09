-- Prove2me | Theorems.Thm_SqrtQueries_taylor_remainder
-- name    : SqrtQueries.taylor_remainder
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:30:28.779091+00:00
-- url     : https://prove2.me/theorems/d74fedb7-947f-4185-abda-7102c687b485
-- title:
--   Proof of Proposition 3.6 — Taylor remainder $\|E\|\le1/8$
-- statement:
--   Let $N\ge1$, $A=(S+S^\dagger)/2$, and let $R$ be a unitary $N\times N$ matrix. Write
--   $$
--   e^{iA/4}Re^{-iA/4}=R+\tfrac14[iA,R]+E ,\qquad [X,Z]=XZ-ZX .
--   $$
--   Then the remainder satisfies
--   $$
--   \|E\|\le\frac18
--   $$
--   in operator norm.
--
--   In the proof of Proposition 3.6 this is applied with $R$ a square root of $D$ and $V_1=e^{iA/4}Re^{-iA/4}$ a square root of $U_1$: to first order, $V_1$ is $R$ plus a commutator that records the differences of adjacent eigenvalues of $R$.
--
--   Differences from the source:
--   - generalization: R a square root of D → R any unitary matrix; reason: every square root of D is unitary (Section 2.1, R = ΣB) and the argument only uses that R(t) is unitary
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), proof of Proposition 3.6, p.19

import Mathlib
import Definitions.Def_SqrtQueries_smearA

open scoped Matrix.Norms.L2Operator

namespace SqrtQueries

/-- **Taylor remainder** in the proof of Proposition 3.6 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.19: writing
`R(1/4) = e^{iA/4} R e^{−iA/4} = R + ¼[iA, R] + E`, the error satisfies `‖E‖ ≤ 1/8`. Here
`A = (S + S†)/2` is the matrix of Definition 3.2 and `R` is a square root of `D`.

**Formalization Note.** The bound is stated for every unitary `R` on `ℂ^N` (`N ≥ 1`); every square
root of `D` is unitary (it is `ΣB`, Section 2.1), so this covers the page's `R`, and the page's
argument uses only "`R(t)` is always unitary". `[X, Z] = XZ − ZX`; the norm is the `L2` operator
norm. -/
theorem taylor_remainder (N : ℕ) [NeZero N] (R : Matrix (Fin N) (Fin N) ℂ)
    (hR : R ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖NormedSpace.exp ((Complex.I / 4) • smearA N) * R *
          NormedSpace.exp ((-Complex.I / 4) • smearA N) - R -
        (1 / 4 : ℂ) • ((Complex.I • smearA N) * R - R * (Complex.I • smearA N))‖ ≤ 1 / 8 := by sorry

end SqrtQueries
