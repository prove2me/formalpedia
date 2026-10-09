-- Prove2me | Theorems.Thm_SymPolyOpt_Quartic_bivariate_quartic_nonneg_iff_sos
-- name    : SymPolyOpt.Quartic.bivariate_quartic_nonneg_iff_sos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:36.569975+00:00
-- url     : https://prove2.me/theorems/5429fe06-36a6-4430-9fd9-f5c02e2c19a9
-- title:
--   Theorem 5.5 proof, p. 23 — a bivariate polynomial of degree ≤ 4 is non-negative iff it is a sum of squares
-- statement:
--   Let $h \in \mathbb R[T_1, T_2]$ have total degree at most $4$. Then
--   $$h(t) \ge 0 \ \text{ for all } t \in \mathbb R^2 \iff h = \sum_{i=1}^k u_i^2 \ \text{ for some } u_1, \dots, u_k \in \mathbb R[T_1, T_2].$$
--
--   This is the step of the proof of Theorem 5.5 that applies Hilbert's theorem to each $f^\omega$.
--
--   **Formalization Note** The page says $f^\omega$ "is of degree 4 in two variables". A substitution can only lower the total degree, and the step needs degree $4$ only as an upper bound, so the statement is posed for total degree $\le 4$. "Sum of squares" is Mathlib's `IsSumSq`.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 23, proof of Theorem 5.5

import Mathlib

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- A real polynomial in two variables of total degree at most 4 is non-negative on `ℝ²`
if and only if it is a sum of squares of polynomials. -/
theorem bivariate_quartic_nonneg_iff_sos (h : MvPolynomial (Fin 2) ℝ) (hdeg : h.totalDegree ≤ 4) :
    (∀ t : Fin 2 → ℝ, 0 ≤ eval t h) ↔ IsSumSq h := by sorry

end SymPolyOpt.Quartic
