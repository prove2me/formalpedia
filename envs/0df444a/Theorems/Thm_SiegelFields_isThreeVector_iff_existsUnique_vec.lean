-- Prove2me | Theorems.Thm_SiegelFields_isThreeVector_iff_existsUnique_vec
-- name    : SiegelFields.isThreeVector_iff_existsUnique_vec
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T00:59:39.107745+00:00
-- url     : https://prove2.me/theorems/9f4c6c41-a733-4e2d-a443-b6b82dd5995e
-- title:
--   3-vectors are exactly the matrices $\frac1{\sqrt2}\begin{pmatrix}V^1&V^2-iV^3\\V^2+iV^3&-V^1\end{pmatrix}$
-- statement:
--   Throughout, $M_2(\mathbb C)$ is the space of complex $2\times2$ matrices, $V^\dagger$ the conjugate transpose, and a **3-vector** is a matrix in $\mathcal V=\{V\in M_2(\mathbb C): V^\dagger=V,\ \operatorname{tr}V=0\}$. A matrix $V\in M_2(\mathbb C)$ is a 3-vector if and only if there is a **unique** $v\in\mathbb R^3$ with
--
--   $$V=\frac1{\sqrt2}\begin{pmatrix}v_1& v_2-iv_3\\ v_2+iv_3&-v_1\end{pmatrix}.$$
--
--   So the book's basis identifies $\mathcal V$ with $\mathbb R^3$.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 p. 111

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem isThreeVector_iff_existsUnique_vec (V : Matrix (Fin 2) (Fin 2) ℂ) :
    IsThreeVector V ↔ ∃! v : Fin 3 → ℝ, V = vecToMatrix v := by sorry
end SiegelFields
