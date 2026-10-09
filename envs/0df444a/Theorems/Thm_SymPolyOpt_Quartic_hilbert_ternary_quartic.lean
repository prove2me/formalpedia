-- Prove2me | Theorems.Thm_SymPolyOpt_Quartic_hilbert_ternary_quartic
-- name    : SymPolyOpt.Quartic.hilbert_ternary_quartic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:37.387225+00:00
-- url     : https://prove2.me/theorems/5393067d-c48e-49a9-8814-db5ce767953e
-- title:
--   §5, p. 23 — Hilbert's theorem: every non-negative ternary quartic form is a sum of squares
-- statement:
--   Let $F \in \mathbb R[X_1, X_2, X_3]$ be a homogeneous polynomial of degree $4$ (a ternary quartic form) with $F(x) \ge 0$ for every $x \in \mathbb R^3$. Then
--   $$F = \sum_{i=1}^{k} h_i^2 \quad \text{for some } h_1, \dots, h_k \in \mathbb R[X_1, X_2, X_3].$$
--
--   This is Hilbert's theorem of 1888. The paper invokes it in the proof of Theorem 5.5; for quartics in more than three variables the statement fails in general (Choi–Lam, Example 5.6).
--
--   **Formalization Note** The page says "ternary quartic polynomial"; this is read as a ternary quartic *form*, the classical statement. Read for inhomogeneous polynomials in three variables of degree 4 the claim is false (these dehomogenize quaternary quartic forms). "Sum of squares" is Mathlib's `IsSumSq`, which includes the empty sum $0$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 23, §5, "By Hilbert's Theorem, every non-negative ternary quartic polynomial is a sum of squares."

import Mathlib

namespace SymPolyOpt.Quartic

open MvPolynomial

/-- Hilbert's theorem (1888): every non-negative ternary quartic form is a sum of squares
of polynomials. -/
theorem hilbert_ternary_quartic (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hnn : ∀ x : Fin 3 → ℝ, 0 ≤ eval x F) : IsSumSq F := by sorry

end SymPolyOpt.Quartic
