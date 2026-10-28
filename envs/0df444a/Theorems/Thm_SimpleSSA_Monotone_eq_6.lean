-- Prove2me | Theorems.Thm_SimpleSSA_Monotone_eq_6
-- name    : SimpleSSA.Monotone.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:05.83714+00:00
-- url     : https://prove2.me/theorems/1f15fccb-33b1-425a-ba46-f3f31c7b7945
-- title:
--   (6), p. 2 — S(ρ_AB ‖ I_A/d_A ⊗ ρ_B) ≤ S(ρ_ABC ‖ I_A/d_A ⊗ ρ_BC) for invertible ρ_ABC
-- statement:
--   Let $\rho_{ABC}$ be an invertible density matrix on a tripartite finite-dimensional system $ABC$, with reduced density matrices $\rho_{AB} = \operatorname{tr}_C\rho_{ABC}$, $\rho_{BC} = \operatorname{tr}_A\rho_{ABC}$ and $\rho_B = \operatorname{tr}_A\rho_{AB}$, and let $d_A$ be the dimension of $A$. Then
--
--   $$S\Big(\rho_{AB}\,\Big\|\,\frac{I_A}{d_A}\otimes\rho_B\Big) \le S\Big(\rho_{ABC}\,\Big\|\,\frac{I_A}{d_A}\otimes\rho_{BC}\Big),$$
--
--   where $S(\cdot\|\cdot)$ is the relative entropy (3).
--
--   By the identity (5), this inequality is the conditional form (2) of strong subadditivity, recast as an inequality between relative entropies; the paper obtains it from the monotonicity (4) by discarding $C$.
--
--   **Formalization Note** The statement assumes $\rho_{ABC}$ invertible (positive definite), which is the scope of the paper's proof (p. 3: "our proof of monotonicity of the relative entropy and of strong subadditivity only applies directly for invertible density matrices"); the general case is the omitted continuity argument and is equivalent to strong subadditivity itself. Tripartite operators are indexed by $(a,(b,c))$. Logarithms are natural.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, p. 2, (6); invertibility assumption p. 3

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone

open TroppMatrixConcentration QAlgorithms WildeQIT

/-- (6), p. 2, for invertible `ρ_ABC` (the §3 assumption, p. 3):
`S(ρ_AB ‖ I_A/d_A ⊗ ρ_B) ≤ S(ρ_ABC ‖ I_A/d_A ⊗ ρ_BC)`, with `ρ_AB = Tr_C ρ_ABC`,
`ρ_BC = Tr_A ρ_ABC`, `ρ_B = Tr_A ρ_AB`. -/
theorem eq_6 {A B C : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef) :
    relEntropy (traceOutC ρ) (maximallyMixed A ⊗ₖ partialTraceLeft (traceOutC ρ)) ≤
      relEntropy ρ (maximallyMixed A ⊗ₖ partialTraceLeft ρ) := by sorry

end SimpleSSA.Monotone
