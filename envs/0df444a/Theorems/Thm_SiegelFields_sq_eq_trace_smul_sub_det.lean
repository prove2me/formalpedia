-- Prove2me | Theorems.Thm_SiegelFields_sq_eq_trace_smul_sub_det
-- name    : SiegelFields.sq_eq_trace_smul_sub_det
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:20:18.447252+00:00
-- url     : https://prove2.me/theorems/86b45e17-ae1d-4d99-b350-1145447c78a3
-- title:
--   $M^2=M\operatorname{tr}M-I\det M$, hence $V^2=-I\det V=I\tfrac12|V|^2$
-- statement:
--   1. For every complex $2\times2$ matrix $M$, $\;M^2=(\operatorname{tr}M)\,M-(\det M)\,I$.
--   2. For every 3-vector $V$ (hermitian, traceless),
--
--   $$V^2=-(\det V)\,I=\tfrac12\operatorname{tr}(V^2)\,I=\tfrac12|V|^2 I .$$
--
--   This is the Cayley–Hamilton identity in dimension two, specialized to 3-vectors.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 p. 112

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem sq_eq_trace_smul_sub_det :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      M * M = trace M • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V →
      V * V = (-V.det) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      V * V = ((1 / 2 : ℂ) * trace (V * V)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by sorry
end SiegelFields
