-- Prove2me | Theorems.Thm_SymPolyOpt_Quartic_theorem_5_5
-- name    : SymPolyOpt.Quartic.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:47.371272+00:00
-- url     : https://prove2.me/theorems/8a8cc332-5416-449a-a3dc-aa52ffb0997f
-- title:
--   Theorem 5.5, p. 23 — a symmetric quartic f is non-negative iff f^ω is a sum of squares for every 2-partition ω
-- statement:
--   Let $n \ge 2$ and let $f \in \mathbb R[X_1, \dots, X_n]$ be a symmetric polynomial of degree $4$. Let $\Omega$ be the set of $2$-partitions $\omega = (\omega_1, \omega_2)$ of $n$ (integers $\omega_1 \ge \omega_2 \ge 1$ with $\omega_1 + \omega_2 = n$), and for $\omega \in \Omega$ let
--   $f^\omega := f(T_1, \dots, T_1, T_2, \dots, T_2) \in \mathbb R[T_1, T_2]$, with $T_1$ repeated $\omega_1$ times and $T_2$ repeated $\omega_2$ times. Then
--   $$f(x) \ge 0 \ \text{ for all } x \in \mathbb R^n \iff f^\omega \text{ is a sum of squares in } \mathbb R[T_1, T_2] \text{ for every } \omega \in \Omega.$$
--
--   Deciding non-negativity of a symmetric quartic in $n$ variables, which is not an SOS question in general (Choi–Lam), thus reduces to at most $\lfloor n/2 \rfloor$ semidefinite feasibility problems in two variables.
--
--   **Formalization Note** The hypothesis $n \ge 2$ is not printed: for $n = 1$ there is no $2$-partition, the right-hand side holds vacuously, and $f = X_1^4 - 1$ is a counterexample. "Of degree 4" is total degree exactly $4$, as printed. "Symmetric" is `MvPolynomial.IsSymmetric`; "sum of squares" is `IsSumSq` in the two-variable polynomial ring; a $2$-partition is a block map (see the setting definition).
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 23, Theorem 5.5

import Mathlib
import Definitions.Def_SymPolyOpt_Quartic_Setting

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- Theorem 5.5: a symmetric polynomial `f ∈ ℝ[X_1, …, X_n]` of degree 4 (`n ≥ 2`) is
non-negative on `ℝ^n` if and only if, for every 2-partition `ω` of `n`, the bivariate polynomial
`f^ω` is a sum of squares in `ℝ[T_1, T_2]`. -/
theorem theorem_5_5 (n : ℕ) (hn : 2 ≤ n) (f : MvPolynomial (Fin n) ℝ)
    (hsym : f.IsSymmetric) (hdeg : f.totalDegree = 4) :
    (∀ x : Fin n → ℝ, 0 ≤ eval x f) ↔
      ∀ b : Fin n → Fin 2, IsBlockMap b → IsSumSq (restrict b f) := by sorry

end SymPolyOpt.Quartic
