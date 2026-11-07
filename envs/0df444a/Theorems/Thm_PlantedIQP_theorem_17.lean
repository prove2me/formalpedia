-- Prove2me | Theorems.Thm_PlantedIQP_theorem_17
-- name    : PlantedIQP.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:56.167707+00:00
-- url     : https://prove2.me/theorems/a5ad9bcf-f5bd-44f7-96bc-4118416cd762
-- title:
--   Theorem 17 — $T^f_u=H^f_u+Q_f$
-- statement:
--   Let $f$ be a cubic polynomial and $u\in\mathbb F_2^n$. The slice $T^f_u(v,w)=T_f(u,v,w)$ of the trilinear form equals the sum of the Hessian slice and the quadratic-part matrix:
--
--   $$
--   T^f_u=H^f_u+Q_f ,
--   $$
--
--   both as matrices in the standard basis and as bilinear forms, $T_f(u,v,w)=v^{\mathsf T}(H^f_u+Q_f)w$.
--
--   The Hessian slices thus form an affine family of alternating matrices indexed by $u$, whose ranks the paper's algorithms for large planted spaces exploit.
--
--   Differences from the source:
--   - encoding: T^f_u = H^f_u + Q_f as bilinear forms → equality of the matrices in the standard basis and, separately, of the bilinear forms v,w ↦ T_f(u,v,w) and v,w ↦ vᵀ(H^f_u+Q_f)w; reason: a bilinear form on 𝔽₂ⁿ is determined by its matrix; both readings are stated
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Theorem 17, p.15

import Mathlib
import Definitions.Def_PlantedIQP_triForm
import Definitions.Def_PlantedIQP_hessSlice

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Theorem 17, p.15: for a cubic polynomial `f` and `u ∈ 𝔽₂ⁿ`, the slice
`T^f_u(v, w) = T_f(u, v, w)` equals `H^f_u + Q_f`: as matrices in the standard basis, and as bilinear
forms, `T_f(u, v, w) = vᵀ (H^f_u + Q_f) w`. -/
theorem theorem_17 {n : ℕ} (f : CubicPoly n) (u : Vec n) :
    sliceMatrix f u = hessSlice f u + quadMatrix f ∧
      ∀ v w : Vec n, triForm f u v w = ∑ i, ∑ j, v i * (hessSlice f u + quadMatrix f) i j * w j := by sorry

end PlantedIQP
