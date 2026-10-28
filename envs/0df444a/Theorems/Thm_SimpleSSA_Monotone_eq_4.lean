-- Prove2me | Theorems.Thm_SimpleSSA_Monotone_eq_4
-- name    : SimpleSSA.Monotone.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:08.97204+00:00
-- url     : https://prove2.me/theorems/ca864458-9bf5-4f50-a11d-119f5c192ffd
-- title:
--   (4), p. 2 — monotonicity of the relative entropy: S(ρ_A‖σ_A) ≤ S(ρ_AB‖σ_AB) for invertible ρ_AB, σ_AB
-- statement:
--   Let $\rho_{AB}$ and $\sigma_{AB}$ be invertible density matrices on a composite finite-dimensional system $AB$, and let $\rho_A = \operatorname{tr}_B\rho_{AB}$ and $\sigma_A = \operatorname{tr}_B\sigma_{AB}$ be their reduced density matrices on $A$. Then
--
--   $$S(\rho_A\|\sigma_A) \le S(\rho_{AB}\|\sigma_{AB}),$$
--
--   where $S(\rho\|\sigma) = \operatorname{tr}(\rho\ln\rho-\rho\ln\sigma)$ is the relative entropy. Discarding part of a composite system can only decrease the relative entropy between two states.
--
--   This is the monotonicity of the relative entropy, from which the paper derives strong subadditivity through (5) and (6). It is proved in §3 (pp. 3–5).
--
--   **Formalization Note** The inequality is stated for invertible (positive definite) $\rho_{AB}$ and $\sigma_{AB}$. This is the paper's own assumption in §3 (p. 3: "our proof of monotonicity of the relative entropy and of strong subadditivity only applies directly for invertible density matrices"); the extension to all density matrices is a continuity argument the paper omits. It also keeps the relative entropy finite, so that its real-valued encoding is the paper's value. Logarithms are natural.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, p. 2, (4); proved in §3, pp. 3–5, for invertible density matrices (p. 3)

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone

open TroppMatrixConcentration QAlgorithms WildeQIT

/-- (4), p. 2, proved in §3 for invertible states (p. 3): monotonicity of the relative entropy
under discarding `B`, `S(ρ_A‖σ_A) ≤ S(ρ_AB‖σ_AB)`. -/
theorem eq_4 {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    relEntropy (partialTraceRight ρ) (partialTraceRight σ) ≤ relEntropy ρ σ := by sorry

end SimpleSSA.Monotone
