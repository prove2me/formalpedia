-- Prove2me | Theorems.Thm_PrivAcq_Central_monotone_minimizer
-- name    : PrivAcq.Central.monotone_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:23.812193+00:00
-- url     : https://prove2.me/theorems/8467302a-ecef-4c1e-a6be-318c2eb3f761
-- title:
--   Proof of Theorem 3, p. 45 — under Assumption 1 the solution of (A36) is weakly decreasing in the privacy cost
-- statement:
--   Fix the model and assume Assumption 1 (each virtual cost $\psi_i$ is increasing on $[a_i,b_i]$). Let $c, c'$ be type profiles in the type space that differ only in coordinate $i$, let $y$ be an optimal solution of (23) at $c$ and $y'$ an optimal solution of (23) at $c'$. Then
--   $$
--   (y_i - y'_i)\big(\psi_i(c_i) - \psi_i(c'_i)\big) \le 0,
--   $$
--   and consequently $c_i < c'_i$ implies $y'_i \le y_i$.
--
--   This is the monotonicity that makes the pointwise minimizer of (23) satisfy the dropped constraint (21), so that the payment identity of Proposition 1 applies to it.
--
--   **Formalization Note** The paper argues for the first coordinate "without loss of generality"; the statement is given for an arbitrary coordinate $i$ and for arbitrary optimal solutions $y$, $y'$ (no uniqueness is assumed).
-- source:
--   Fallah, Makhdoumi, Malekian, Ozdaglar, arXiv:2201.03968v2, p. 45, proof of Theorem 3

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

namespace PrivAcq.Central

theorem monotone_minimizer {n : ℕ} (S : Setting n) (hA1 : S.Assumption1)
    (c c' y y' : Fin n → ℝ) (hc : c ∈ S.types) (hc' : c' ∈ S.types) (i : Fin n)
    (hcc' : ∀ j : Fin n, j ≠ i → c j = c' j)
    (hy : IsOpt23 S c y) (hy' : IsOpt23 S c' y') :
    (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) ≤ 0 ∧ (c i < c' i → y' i ≤ y i) := by sorry

end PrivAcq.Central
