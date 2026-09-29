-- Prove2me | Theorems.Thm_SiegelFields_det_vecToMatrix
-- name    : SiegelFields.det_vecToMatrix
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:16:07.516253+00:00
-- url     : https://prove2.me/theorems/ce0774c2-eafd-4c46-b6d4-773e642c8a58
-- title:
--   In components: $\det V=-\tfrac12(V^i)^2$ and $\operatorname{tr}(V^2)=(V^i)^2$
-- statement:
--   For every $v\in\mathbb R^3$, with $V(v)=\frac1{\sqrt2}\begin{pmatrix}v_1& v_2-iv_3\\ v_2+iv_3&-v_1\end{pmatrix}$,
--
--   $$\det V(v)=-\tfrac12\sum_{i=1}^3 v_i^2,\qquad \operatorname{tr}\big(V(v)^2\big)=\sum_{i=1}^3 v_i^2 .$$
--
--   So the norm $|V|^2$ is the usual squared Euclidean length of the component vector.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 pp. 111–112

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem det_vecToMatrix (v : Fin 3 → ℝ) :
    (vecToMatrix v).det = ((-(1 / 2 : ℝ) * ∑ i, v i ^ 2 : ℝ) : ℂ) ∧
      trace (vecToMatrix v * vecToMatrix v) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by sorry
end SiegelFields
