-- Prove2me | Theorems.Thm_PSDPolyApprox_nonneg_factorization_lower_bound
-- name    : PSDPolyApprox.nonneg_factorization_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:55.117275+00:00
-- url     : https://prove2.me/theorems/0ca57f26-5f02-4664-9551-b56d62c581ca
-- title:
--   §3, pp.5–7 — every nonnegative factorization of the matrix (4) has at least $e^{C\sqrt n}$ terms
-- statement:
--   For every $0<\epsilon<1$ there is a constant $C>0$ such that for every $n\ge2$: if the $2^n\times2^n$ matrix (4),
--   $$
--   M_\epsilon(x,y)=(1-\epsilon)\frac1n(x^{\mathsf T}y)^2+\epsilon\qquad(x,y\in\{-1,1\}^n),
--   $$
--   is a sum of $N$ entrywise nonnegative rank-one matrices, then
--   $$
--   N\ge e^{C\sqrt n}.
--   $$
--   In other words $\operatorname{rank}_+(M_\epsilon)\ge e^{C\sqrt n}$. Combined with the factorization of size $\operatorname{xc}(Q)$ and the reduction to $A=\frac1nI_n$, this proves Theorem 1.
--
--   **Formalization Note** The constant $C$ depends only on $\epsilon$ and is chosen before $n$.
--
--   Differences from the source:
--   - generalization: ǫ = 1/3 ("For concreteness we will assume in the rest of the proof that ǫ = 1/3 (it is easy to see that the proof works with any constant 0 < ǫ < 1)") → every ε ∈ (0, 1), with C depending on ε; reason: Theorem 1 is stated for every ε and the paper asserts that the proof covers it; specializes to ε = 1/3
--   - reading: "C > 0 is an absolute positive constant", for large enough n → C > 0 depends on ε only and the bound holds for every n ≥ 2; reason: C is absolute in the paper because ε is fixed; for n ≥ 2 the matrix is not rank one, so N ≥ 2, and finitely many small n are absorbed by shrinking C
--   - encoding: H_n = {−1, 1}^n and the uniform measure µ → functions Fin n → ℤˣ; µ(S) = |S|/2^n and E[f] = 2^{−n} Σ f; reason: ℤˣ = {±1}; same instances
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, pp.5–7 (from "Assume we can write the matrix (4) as a sum of N rank-one nonnegative terms", p.5, to "This completes the proof.", p.7)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_slackSubmatrix

open ExtensionComplexity.TSP

namespace PSDPolyApprox

/-- **Every nonnegative factorization of the matrix (4) has `e^{C√n}` terms.**
Fawzi, arXiv:1811.09649v1, §3, pp.5–7: "Assume we can write the matrix (4) as a sum of N rank-one
nonnegative terms: … This yields |I|e−√n/2 + |Ic| exp(−c√n) ≥ 1 and so this shows that we must
have |I| + |Ic| ≥ eC√n where C > 0 is an absolute positive constant. This completes the proof."

For every `0 < ε < 1` there is `C > 0` such that for every `n ≥ 2` and `N`, if the `2ⁿ × 2ⁿ`
matrix `(x, y) ↦ (1 − ε)(1/n)(xᵀy)² + ε` is a sum of `N` nonnegative rank-one matrices, then
`N ≥ e^{C√n}`.

**Formalization Note.** `C` depends on `ε` only (the paper fixes `ε = 1/3`, so its constant is
"absolute") and is chosen before `n`. `n ≥ 2` replaces "for large enough n": the matrix is not
rank one for `n ≥ 2`, so `N ≥ 2` there. -/
theorem nonneg_factorization_lower_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ N : ℕ,
      HasNonnegFactorization (slackSubmatrix ε n) N → Real.exp (C * Real.sqrt n) ≤ N := by sorry

end PSDPolyApprox
