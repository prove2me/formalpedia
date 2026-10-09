-- Prove2me | Theorems.Thm_SymPolyOpt_Putinar_if_computation
-- name    : SymPolyOpt.Putinar.if_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:22.259181+00:00
-- url     : https://prove2.me/theorems/6a2fb370-ed4b-4449-b12f-f894baeb2e27
-- title:
--   Theorem 3.2 proof (if), p. 11 — for G-linear L^G and G-invariant g_j, 𝓛^G_{g_j}(h, h) = L^G(h² g_j)
-- statement:
--   Let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$, let $L^G:\mathbb R[X]\to\mathbb R$ be $G$-linear and let $g\in\mathbb R[X]$ be $G$-invariant. Then for every $h\in\mathbb R[X]$ the symmetrized localizing form (3.1) satisfies
--   $$\mathcal L^G_{g}(h,h)=L^G\Big(\frac1{|G|}\sum_{\sigma\in G}(h^2)^\sigma g\Big)=L^G(h^2g).$$
--
--   In the "if" half of Theorem 3.2, this turns positive semidefiniteness of the forms $\mathcal L^G_{g_j}$ into the hypothesis $L^G(h^2g_j)\ge0$ of Putinar's Theorem 2.2.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 11, proof of Theorem 3.2, If part (display)

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Putinar

open MvPolynomial

theorem if_computation {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsGLinear G L)
    (gj : MvPolynomial (Fin n) ℝ) (hgj : IsGInvariant G gj) (h : MvPolynomial (Fin n) ℝ) :
    symForm G L gj h h = L (h * h * gj) := by sorry

end SymPolyOpt.Putinar
