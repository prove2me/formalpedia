-- Prove2me | Theorems.Thm_WildeQIT_QMemory_eq_11_212
-- name    : WildeQIT.QMemory.eq_11_212
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:29.900691+00:00
-- url     : https://prove2.me/theorems/e88346e3-9bd6-43e8-97f3-b211e143ceb9
-- title:
--   Eq. (11.212) — uncertainty relation with the purifying system $H(X|B)_\sigma+H(Z|E)_\omega\ge\log(1/c)$
-- statement:
--   Let $\rho_{AB}$ be a state, $|\varphi^\rho\rangle_{ABE}$ a purification of it (so $\mathrm{Tr}_E\{\varphi^\rho_{ABE}\}=\rho_{AB}$), and $\{\Lambda^x_A\}$, $\{\Gamma^z_A\}$ two POVMs on $A$. Let $\sigma_{XB}$ be the post-measurement state (11.208) of $\{\Lambda^x_A\}$ on $\rho_{AB}$, $\omega_{ZE}=\sum_z|z\rangle\langle z|_Z\otimes\mathrm{Tr}_{AB}\{(\Gamma^z_A\otimes I_{BE})\varphi^\rho_{ABE}\}$ as in (11.213), and $c$ the incompatibility (11.210). Then
--
--   $$
--   H(X|B)_\sigma+H(Z|E)_\omega\ge\log(1/c).
--   $$
--
--   This is the relation the book proves first; Theorem 11.9.5 follows from it when one of the POVMs is rank-one. No rank-one assumption is needed here.
--
--   **Formalization Note** The purification is a vector $\varphi$ on $(A\times B)\times E$, for an arbitrary finite system $E$, with $\mathrm{Tr}_E|\varphi\rangle\langle\varphi|=\rho_{AB}$ (published `WildeQIT.partialTraceRight`); this forces $\|\varphi\|=1$. Logarithms are base 2.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces and their tensor products → complex matrices indexed by finite types, $\mathcal H_A\otimes\mathcal H_B$ indexed by `A × B` (Kronecker convention); reason: the book works in finite dimensions throughout; same objects.
--   - encoding: a purification |φ^ρ⟩_ABE of ρ_AB → a vector φ on (A × B) × E with Tr_E |φ⟩⟨φ| = ρ_AB, E any finite type; reason: the definition of purification; normalization follows from Tr ρ = 1.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 11.9.5, eqs. (11.212)–(11.213), p. 355

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_qCondEntropy
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_QMemory_postMeasState
import Definitions.Def_WildeQIT_QMemory_purMeasState
import Definitions.Def_WildeQIT_QMemory_incompatibility

namespace WildeQIT.QMemory

/-- **Eq. (11.212), the uncertainty relation with the purifying system** (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Theorem 11.9.5, p. 355). Let `ρ_AB` be a
state, `|φ^ρ⟩_ABE` a purification of it, and `{Λ^x_A}`, `{Γ^z_A}` POVMs. With `σ_XB` as in
(11.208), `ω_ZE` as in (11.213) and `c` as in (11.210),
`H(X|B)_σ + H(Z|E)_ω ≥ log(1/c)` (11.212).

**Formalization Note** The purification is a vector `φ` on `(A × B) × E`, for any finite
system `E`, with `Tr_E{|φ⟩⟨φ|} = ρ_AB` (published `WildeQIT.partialTraceRight`); this forces
`‖φ‖ = 1`. `log` is base 2. -/
theorem eq_11_212 {A B E X Z : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (φ : (A × B) × E → ℂ)
    (hφ : WildeQIT.partialTraceRight (Matrix.vecMulVec φ (star φ)) = ρ)
    (Λ : X → Matrix A A ℂ) (Γ : Z → Matrix A A ℂ) (hΛ : IsPOVM Λ) (hΓ : IsPOVM Γ) :
    Real.logb 2 (1 / incompatibility Λ Γ) ≤
      qCondEntropy (postMeasState Λ ρ) +
        qCondEntropy (purMeasState Γ (Matrix.vecMulVec φ (star φ))) := by sorry

end WildeQIT.QMemory
