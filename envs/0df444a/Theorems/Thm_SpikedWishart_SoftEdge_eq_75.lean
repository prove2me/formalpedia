-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_75
-- name    : SpikedWishart.SoftEdge.eq_75
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:38:23.33204+00:00
-- url     : https://prove2.me/theorems/89144af5-b396-43fa-a8c2-ca1289a80380
-- title:
--   (75), p. 1658 — Hankel's formula (2πi)⁻¹∮ e^w w^{−a} dw = 1/(a−1)! = 1/Γ(a)
-- statement:
--   Let $a\ge1$ be an integer and let $\Sigma$ be a counterclockwise circle enclosing the origin (centre $c\in\mathbb C$, radius $\rho>|c|$). Then
--   $$
--   \frac1{2\pi i}\oint_\Sigma\frac{e^w}{w^a}\,dw=\frac1{(a-1)!}=\frac1{\Gamma(a)} .
--   $$
--
--   This is the contour-integral representation of $1/\Gamma(a)$ that turns the monomials $\zeta^{j-1+\nu}$ into contour integrals in the proof of Proposition 2.1 ((76)–(81)).
--
--   **Formalization Note** The paper allows any simple closed contour around $0$; it is represented here by circles enclosing $0$, since general Jordan curves are not available in Mathlib.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1658, §2.1, (75)

import Mathlib
open Complex

namespace SpikedWishart.SoftEdge

theorem eq_75 (a : ℕ) (ha : 1 ≤ a) (c : ℂ) (ρ : ℝ) (hc : ‖c‖ < ρ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (∮ w in C(c, ρ), exp w / w ^ a) = 1 / ((a - 1).factorial : ℂ) ∧
      1 / ((a - 1).factorial : ℂ) = 1 / Gamma (a : ℂ) := by sorry

end SpikedWishart.SoftEdge
