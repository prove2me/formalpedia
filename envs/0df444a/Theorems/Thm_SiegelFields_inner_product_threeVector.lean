-- Prove2me | Theorems.Thm_SiegelFields_inner_product_threeVector
-- name    : SiegelFields.inner_product_threeVector
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:17:47.621105+00:00
-- url     : https://prove2.me/theorems/cab6d7bb-886c-403b-9f5b-203f04584cb5
-- title:
--   Inner product of 3-vectors: $V\cdot W=\det V+\det W-\det(V+W)=\operatorname{tr}(VW)$ and $\{V,W\}=(V\cdot W)I$
-- statement:
--   Throughout, $M_2(\mathbb C)$ is the space of complex $2\times2$ matrices, $V^\dagger$ the conjugate transpose, and a **3-vector** is a matrix in $\mathcal V=\{V\in M_2(\mathbb C): V^\dagger=V,\ \operatorname{tr}V=0\}$. For all $V,W\in\mathcal V$,
--
--   $$\det V+\det W-\det(V+W)=\operatorname{tr}(VW),\qquad VW+WV=\operatorname{tr}(VW)\,I .$$
--
--   The common value $V\cdot W=\operatorname{tr}(VW)$ is the inner product obtained by polarizing the norm $|V|^2$, and the anticommutator of two 3-vectors is that inner product times the identity.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 pp. 111–112

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem inner_product_threeVector (V W : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) (hW : IsThreeVector W) :
    V.det + W.det - (V + W).det = trace (V * W) ∧
      V * W + W * V = trace (V * W) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by sorry
end SiegelFields
