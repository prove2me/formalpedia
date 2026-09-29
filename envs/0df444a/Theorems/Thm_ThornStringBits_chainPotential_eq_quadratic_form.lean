-- Prove2me | Theorems.Thm_ThornStringBits_chainPotential_eq_quadratic_form
-- name    : ThornStringBits.chainPotential_eq_quadratic_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:37:10.900277+00:00
-- url     : https://prove2.me/theorems/d6e4447f-4485-48a0-8200-16caee909ba2
-- title:
--   The bond potential $\sum_i (x_{i+1}-x_i)^2$ is the quadratic form $x^{\mathsf T} L_M x$
-- statement:
--   For every $M\in\mathbb N$ and every configuration $x=(x_0,\dots,x_{M-1})\in\mathbb R^M$ of transverse bit positions,
--   $$ \sum_{i=0}^{M-1}\bigl(x_{(i+1)\bmod M}-x_i\bigr)^2 \;=\; x^{\mathsf T} L_M\, x = \sum_{i,j}x_i (L_M)_{ij} x_j, $$
--   where $L_M$ is the cyclic Laplacian of the mission's definition file.
--
--   This identifies the potential term of Thorn's Hamiltonian $P^-=\frac1\epsilon\sum_i\frac1{2T_0}(-\nabla_i^2+T_0^2(x_{i+1}-x_i)^2)$ (p. 4) with a quadratic form, so that the classical equations of motion are $\ddot x=-\epsilon^{-2}L_M x$.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, pp. 4–5.

import Definitions.Def_ThornStringBits_Defs
import Mathlib

open Real Matrix

namespace ThornStringBits

theorem chainPotential_eq_quadratic_form (M : ℕ) (x : Fin M → ℝ) :
    chainPotential M x = x ⬝ᵥ (cycLaplacian M *ᵥ x) := by sorry

end ThornStringBits
