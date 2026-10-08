-- Prove2me | Theorems.Thm_VBSDP_Potential_duality_gap_32
-- name    : VBSDP.Potential.duality_gap_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:31.108901+00:00
-- url     : https://prove2.me/theorems/413ad9da-8cf8-485d-8174-3a6091f5715b
-- title:
--   (32) — the duality gap equals Tr F(x)Z
-- statement:
--   Let $F(x)=F_0+\sum_i x_iF_i$ be the affine matrix of the primal semidefinite program, with symmetric data. Suppose $F(x)\succeq0$ and $Z\succeq0$, and $Z$ satisfies the dual equations $\operatorname{Tr}(F_iZ)=c_i$. Then the **duality gap** between the primal objective $c^Tx$ and the dual objective $-\operatorname{Tr}(F_0Z)$ is
--
--   $$\eta=c^Tx+\operatorname{Tr}(F_0Z)=\operatorname{Tr}(F(x)Z).$$
--
--   This identifies the trace quantity used by the potential and by Theorem 5.1 with an objective gap.
--
--   **Formalization Note** Positive semidefiniteness includes symmetry in Mathlib. $F_0$ is separate from the zero-based `Fin m` family of variable matrices.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 64 (PDF p. 16), (32), https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Potential

/-- Equation (32): the primal-dual objective difference equals the matrix trace. -/
theorem duality_gap_32 {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : (VBSDP.Duality.lmi F₀ F x).PosSemidef) (hZ : Z.PosSemidef)
    (hdual : ∀ i, (F i * Z).trace = c i) :
    c ⬝ᵥ x + (F₀ * Z).trace = (VBSDP.Duality.lmi F₀ F x * Z).trace := by sorry

end VBSDP.Potential
