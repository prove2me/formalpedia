-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_4
-- name    : SWSSNet.Diffusion.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:23.900062+00:00
-- url     : https://prove2.me/theorems/3447e158-838e-45c7-8e0f-2ce514dbe9f3
-- title:
--   Theorem 4 (ϑ_p half of (47)) — ϑ_p = −⟨e,B₁⁻¹h⟩/⟨e,B₁⁻¹p⟩
-- statement:
--   Let $B_1$ be the matrix of (38) for a pool $\hat\jmath$, $h$ the vector (12), and $p$ a positive probability vector. Then the SWSS parameter satisfies
--   $$
--   \vartheta_p=-\frac{\langle e,B_1^{-1}h\rangle}{\langle e,B_1^{-1}p\rangle}.
--   $$
--
--   This expresses the LP value $\vartheta_p$ through the coefficients of the limiting diffusion. It identifies $\vartheta_p$ with the "spare capacity" $-\langle e,B_1^{-1}h\rangle$, up to the positive factor $\langle e,B_1^{-1}p\rangle$. The transience proof of Theorem 5 and the recentring of Remark 8 use it.
--
--   **Formalization Note** Only the limiting half of (47) is posed. The second half, for the $n$th system with $B^n_1$ and $h^n$, needs the prelimit model and is not stated.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 20, Theorem 4, (47) (first identity)

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 4, p. 20 (the `ϑ_p` half of (47)): for the matrix `B₁` of any pool `ĵ` and every
positive `p ∈ ∆_I`, `ϑ_p = −⟨e, B₁⁻¹h⟩ / ⟨e, B₁⁻¹p⟩`. -/
theorem theorem_4 {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    swss N p = -(∑ i, ((B1 N ĵ)⁻¹ *ᵥ hvec N) i) / ∑ i, ((B1 N ĵ)⁻¹ *ᵥ p) i := by sorry

end SWSSNet.Diffusion
