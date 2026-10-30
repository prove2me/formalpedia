-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_23
-- name    : ShorEBAdditivity.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:09.696212+00:00
-- url     : https://prove2.me/theorems/487925ed-e328-4d0b-877c-0ee5d57fd229
-- title:
--   Eq. (23): $H(\sigma_{ABC}) - H(\sigma_{BC}) = \sum_j q_j H(\Psi(|a_j\rangle\langle a_j|))$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ be a quantum channel, $q_1,\dots,q_m\ge 0$, and $|a_j\rangle\in\mathcal H_A$, $|b_j\rangle\in\mathcal H_{B'}$ unit vectors. For the flagged state
--
--   $$
--   \sigma_{ABC} = \sum_j q_j\,\Psi(|a_j\rangle\langle a_j|)\otimes|b_j\rangle\langle b_j|\otimes|j\rangle\langle j|
--   $$
--
--   of (19) and its marginal $\sigma_{BC}$ (trace over the $A'$ register),
--
--   $$
--   H(\sigma_{ABC}) - H(\sigma_{BC}) = \sum_j q_j\, H\big(\Psi(|a_j\rangle\langle a_j|)\big).
--   $$
--
--   This identifies the middle terms of strong subadditivity (20) with the average output entropy of $\Psi$ on the pure states $|a_j\rangle$.
--
--   **Formalization Note** $\sigma_{ABC}$ is `sigmaABC Ψ q a b` on $(A'\times B')\times C$; $\sigma_{BC}$ is `traceLeft` after reassociating to $A'\times(B'\times C)$ with `Equiv.prodAssoc`. Entropy in bits.
--
--   Differences from the source:
--   - generalization: q_ij, |a_ij⟩, |b_ij⟩ from the decomposition (18) of (I ⊗ Φ)(ρ_i) → any q_j ≥ 0 and unit vectors a_j, b_j; reason: σ_ABC is defined from q, a, b alone, and the data of (18) satisfy these conditions
--   - encoding: quantum channel (CPTP map) → IsChannel Ψ (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
--   - encoding: |j⟩ an orthonormal set (the flag register C) → the standard basis vectors of ℂ^m, |j⟩⟨j| = Matrix.single j j 1 on Fin m; reason: entropy is invariant under the unitary taking one orthonormal set to another; same values
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (23), p.4, with eq. (11), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ShorEBAdditivity_sigmaABC

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (23), p.4: "H(σABC) − H(σBC) = Σ_j qij H(Ψ(|aij⟩⟨aij|))", the
Theorem 2 instance of eq. (11), p.3.

Let `Ψ` be a channel, `q_j ≥ 0`, and `|a_j⟩`, `|b_j⟩` unit vectors. For the flagged state
`σ_ABC = Σ_j q_j Ψ(|a_j⟩⟨a_j|) ⊗ |b_j⟩⟨b_j| ⊗ |j⟩⟨j|` of (19),
`H(σ_ABC) − H(σ_BC) = Σ_j q_j H(Ψ(|a_j⟩⟨a_j|))`.

**Formalization Note.** `σ_ABC` is `sigmaABC Ψ q a b` on `(A' × B') × Fin m`; `σ_BC` traces out
the `A'` register after reassociating to `A' × (B' × Fin m)` along `Equiv.prodAssoc`. `H` is
`QAlgorithms.vnEntropy` (bits). In the paper `q`, `a`, `b` come from the decomposition (18);
the identity only uses that the weights are nonnegative and the vectors have unit length. -/
theorem eq_23 {A A' B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] (Ψ : Superop A A') (hΨ : IsChannel Ψ) {m : ℕ}
    (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) (a : Fin m → EuclideanSpace ℂ A) (ha : ∀ j, ‖a j‖ = 1)
    (b : Fin m → EuclideanSpace ℂ B') (hb : ∀ j, ‖b j‖ = 1) :
    vnEntropy (sigmaABC Ψ q a b) -
        vnEntropy (traceLeft ((sigmaABC Ψ q a b).reindex (Equiv.prodAssoc A' B' (Fin m))
          (Equiv.prodAssoc A' B' (Fin m)))) =
      ∑ j, q j * vnEntropy (Ψ (pureDensity (a j))) := by sorry

end ShorEBAdditivity
