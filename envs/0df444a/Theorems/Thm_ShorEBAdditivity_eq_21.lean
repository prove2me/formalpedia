-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_21
-- name    : ShorEBAdditivity.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:55.728067+00:00
-- url     : https://prove2.me/theorems/4275683b-08f8-472b-ba6c-b11b18a61c67
-- title:
--   Eq. (21) via (10): $\sigma_{AB} = \sum_j q_j\Psi(|a_j\rangle\langle a_j|)\otimes|b_j\rangle\langle b_j| = (\Psi\otimes\Phi)(\rho)$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ and $\Phi : M_B\to M_{B'}$ be quantum channels and $\rho$ a density matrix on $\mathcal H_A\otimes\mathcal H_B$. Suppose
--
--   $$
--   (I\otimes\Phi)(\rho) = \sum_j q_j\, |a_j\rangle\langle a_j|\otimes|b_j\rangle\langle b_j|
--   $$
--
--   (the decomposition (18)), and let $\sigma_{ABC} = \sum_j q_j \Psi(|a_j\rangle\langle a_j|)\otimes|b_j\rangle\langle b_j|\otimes|j\rangle\langle j|$ be the flagged state (19). Then its marginal $\sigma_{AB} = \operatorname{Tr}_C\sigma_{ABC}$ satisfies
--
--   $$
--   \sigma_{AB} = \sum_j q_j\, \Psi(|a_j\rangle\langle a_j|)\otimes|b_j\rangle\langle b_j| = (\Psi\otimes\Phi)(\rho).
--   $$
--
--   In particular $H(\sigma_{AB}) = H((\Psi\otimes\Phi)(\rho))$, which is (21): the left-hand side of strong subadditivity (20) is the output entropy to be bounded below.
--
--   **Formalization Note** $\sigma_{AB}$ is `traceRight (sigmaABC Ψ q a b)`; $\Psi\otimes\Phi$ is `tensorChannel Ψ Φ`; the decomposition (18) is the hypothesis `hdec`.
--
--   Differences from the source:
--   - generalization: Φ entanglement breaking, with q_ij, |a_ij⟩, |b_ij⟩ from (18) → any channel Φ and any q, a, b with (I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|; reason: (18) is the only use of entanglement breaking in the proof, and eq_18 supplies such a decomposition for every entanglement-breaking channel
--   - generalization: ρ_i a signal state of the optimal ensemble (17) → any density matrix ρ on A × B; reason: the identity uses only that ρ_i is a state
--   - generalization: H(σAB) = H((Ψ ⊗ Φ)(ρi)) → the two matrix identities of (10), σ_AB = Σ_j q_j Ψ(|a_j⟩⟨a_j|) ⊗ |b_j⟩⟨b_j| = (Ψ ⊗ Φ)(ρ); reason: equal matrices have equal entropy, so this implies (21); the page derives (21) "as before" from (10)
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: |j⟩ an orthonormal set (the flag register C) → the standard basis vectors of ℂ^m, |j⟩⟨j| = Matrix.single j j 1 on Fin m; reason: entropy is invariant under the unitary taking one orthonormal set to another; same values
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (21), p.4, with eq. (10), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorEBAdditivity_sigmaABC

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (21), p.4 ("As before, H(σAB) = H((Ψ ⊗ Φ)(ρi))"), proved through
the two lines of eq. (10), p.3: `σ_AB = Σ_j q_j Ψ(|a_j⟩⟨a_j|) ⊗ |b_j⟩⟨b_j| = (Ψ ⊗ Φ)(ρ)`.

Let `Ψ`, `Φ` be channels and `ρ` a density matrix on `A ⊗ B` with
`(I ⊗ Φ)(ρ) = Σ_j q_j |a_j⟩⟨a_j| ⊗ |b_j⟩⟨b_j|` (the decomposition (18)). Then the marginal
`σ_AB = Tr_C σ_ABC` of the flagged state (19) equals `Σ_j q_j Ψ(|a_j⟩⟨a_j|) ⊗ |b_j⟩⟨b_j|`, and this
equals `(Ψ ⊗ Φ)(ρ)`. In particular `σ_AB = (Ψ ⊗ Φ)(ρ)`, so `H(σ_AB) = H((Ψ ⊗ Φ)(ρ))`.

**Formalization Note.** The decomposition (18) is a hypothesis (`hdec`); entanglement breaking
is used in the paper only to obtain it. `σ_ABC` is `sigmaABC Ψ q a b` on `(A' × B') × Fin m`, so
`σ_AB = traceRight σ_ABC` (trace over the flag register). `Ψ ⊗ Φ` is `tensorChannel Ψ Φ`. No
condition on `q`, `a`, `b` beyond `hdec` is needed. -/
theorem eq_21 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) {m : ℕ} (q : Fin m → ℝ)
    (a : Fin m → EuclideanSpace ℂ A) (b : Fin m → EuclideanSpace ℂ B')
    (hdec : idTensorSuperop Φ ρ = ∑ j, (q j : ℂ) • (pureDensity (a j) ⊗ₖ pureDensity (b j))) :
    traceRight (sigmaABC Ψ q a b) = ∑ j, (q j : ℂ) • (Ψ (pureDensity (a j)) ⊗ₖ pureDensity (b j)) ∧
      ∑ j, (q j : ℂ) • (Ψ (pureDensity (a j)) ⊗ₖ pureDensity (b j)) = tensorChannel Ψ Φ ρ := by sorry

end ShorEBAdditivity
