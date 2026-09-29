-- Prove2me | Theorems.Thm_SiegelFields_threeVector_norm_sq
-- name    : SiegelFields.threeVector_norm_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T00:53:45.065976+00:00
-- url     : https://prove2.me/theorems/790a6d0c-949c-427e-add4-0500f99bf982
-- title:
--   The norm of a 3-vector: $|V|^2=-2\det V=\operatorname{tr}(V^2)$ is positive definite
-- statement:
--   Throughout, $M_2(\mathbb C)$ is the space of complex $2\times2$ matrices, $V^\dagger$ the conjugate transpose, and a **3-vector** is a matrix in $\mathcal V=\{V\in M_2(\mathbb C): V^\dagger=V,\ \operatorname{tr}V=0\}$. For every $V\in\mathcal V$:
--
--   1. $-2\det V=\operatorname{tr}(V^2)$;
--   2. $\operatorname{tr}(V^2)$ is a non-negative real number;
--   3. $\operatorname{tr}(V^2)=0$ if and only if $V=0$.
--
--   $$|V|^2:=-2\det V=\operatorname{tr}(V^2)\ \ge 0,\qquad |V|^2=0\iff V=0.$$
--
--   This makes $|V|^2$ a positive definite quadratic form on $\mathcal V$, the Euclidean norm of the 3-vector.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 p. 111

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem threeVector_norm_sq (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : IsThreeVector V) :
    -2 * V.det = trace (V * V) ∧ (trace (V * V)).im = 0 ∧ 0 ≤ (trace (V * V)).re ∧
      (trace (V * V) = 0 ↔ V = 0) := by sorry
end SiegelFields
