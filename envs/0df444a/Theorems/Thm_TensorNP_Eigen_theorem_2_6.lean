-- Prove2me | Theorems.Thm_TensorNP_Eigen_theorem_2_6
-- name    : TensorNP.Eigen.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:17.699891+00:00
-- url     : https://prove2.me/theorems/aa0248d9-3581-408d-b498-eb636d9aeff9
-- title:
--   Theorem 2.6 — graph 3-colorability reduces to quadratic feasibility over $\mathbb R$ and over $\mathbb C$
-- statement:
--   Let $F=\mathbb R$ or $F=\mathbb C$. Graph 3-colorability is polynomial-time many-one reducible to quadratic feasibility over $F$ (Problem 2.2): there is a function $f$, computable by a Turing machine in time polynomial in the length of its input, such that for every binary string $w$,
--
--   $$w\in\textsf{3-COL}\iff f(w)\in\textsf{QF}_F.$$
--
--   Here $\textsf{3-COL}$ is the set of binary codes of simple graphs having a proper 3-coloring, and $\textsf{QF}_F$ is the set of binary codes of systems of rational matrices $A_1,\dots,A_m\in\mathbb Q^{n\times n}$ for which there is $\mathbf 0\ne\mathbf x\in F^n$ with $\mathbf x^\top A_i\mathbf x=0$ for $i=1,\dots,m$. Both statements, for $\mathbb R$ and for $\mathbb C$, are asserted.
--
--   Since graph 3-colorability is NP-complete (Karp 1972, cited by the paper and not formalized here), quadratic feasibility over $\mathbb R$ and over $\mathbb C$ is NP-hard.
--
--   **Formalization Note** "Polynomially reducible" is stated as Cook's polynomial-time many-one reducibility (`CookPvsNP.PolyReducible`), which implies the oracle notion of the paper's §1.4. Languages are those of the definition file.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:13, Theorem 2.6 (proof p. 0:15)

import Mathlib
import Definitions.Def_TensorNP_Eigen_Defs

namespace TensorNP.Eigen

open CookPvsNP

/-- Theorem 2.6: graph 3-colorability is polynomial-time many-one reducible to quadratic
feasibility (Problem 2.2) over `ℝ` and over `ℂ`. -/
theorem theorem_2_6 :
    PolyReducible threeColLang (quadFeasLang ℝ) ∧
      PolyReducible threeColLang (quadFeasLang ℂ) := by sorry

end TensorNP.Eigen
