-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_fact_3_2
-- name    : PassiveAdiabaticFT.Thermal.fact_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:16.283258+00:00
-- url     : https://prove2.me/theorems/91e555cc-5286-485b-96c7-5dc24f79f1c7
-- title:
--   Fact 3.2 — the frequency components of a Pauli resolve the identity
-- statement:
--   Let $H$ be a Hermitian matrix with spectral projectors $\Pi_\lambda$ and let $F$ satisfy $F^\dagger F=I$ (for instance a single-qubit Pauli). With the frequency components $F_\omega=\sum_{\lambda'-\lambda=\omega}\Pi_\lambda F\Pi_{\lambda'}$,
--   $$\sum_\omega F_\omega^\dagger F_\omega=I,\qquad(3.18)$$
--   the sum over all Bohr frequencies $\omega$ of $H$.
--
--   Applied to $H=H(t)$ and $F=F_\alpha^{(i)}$ this bounds the total jump rate out of the bad sector in Lemma 3.1.
--
--   Differences from the source:
--   - reading: For any ω, i it is the case that Σ_ω F^{(i)†}_{α,ω} F^{(i)}_{α,ω} = I → for every Hamiltonian and operator (hence every α, i and time t), the sum over all Bohr frequencies; reason: ω is summed in (3.18); the free indices are α, i and t
--   - generalization: H = H(t) of (3.1) and F = F_α^{(i)} a single-qubit Pauli → any Hermitian H and any F with F†F = I; reason: the proof (3.19) uses only orthogonality of the spectral projectors and F†F = I; the source case is an instance
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 22, Fact 3.2 (3.18)–(3.19)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Operators

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Fact 3.2 (p. 22), for any Hermitian `H` and any `F` with `F† F = I` (in particular a Pauli):
`Σ_ω F_ω† F_ω = I`, the sum over all Bohr frequencies of `H`. -/
theorem fact_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] (H F : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hF : Fᴴ * F = 1) :
    ∑ ω ∈ bohrFreqs H, (bohrComp H F ω)ᴴ * bohrComp H F ω = 1 := by sorry

end PassiveAdiabaticFT.Thermal
