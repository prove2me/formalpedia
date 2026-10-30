-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_28
-- name    : ShorEBAdditivity.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:51.465933+00:00
-- url     : https://prove2.me/theorems/b8281797-8b5c-46e7-8421-49df7c4c7da2
-- title:
--   Eq. (28): $\chi^*(\Psi\otimes\Phi) \le \chi^*(\Psi) + \chi^*(\Phi)$ for entanglement-breaking $\Phi$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ be an arbitrary quantum channel and $\Phi : M_B\to M_{B'}$ an entanglement-breaking quantum channel, all spaces finite-dimensional. Then the Holevo–Schumacher–Westmoreland capacity is subadditive on this pair:
--
--   $$
--   \chi^*(\Psi\otimes\Phi) \le \chi^*(\Psi) + \chi^*(\Phi).
--   $$
--
--   Here $\chi^*(\Psi\otimes\Phi)$ is maximized over all ensembles of density matrices on $\mathcal H_A\otimes\mathcal H_B$, entangled inputs included. Together with the general superadditivity (4) this gives Theorem 2.
--
--   **Formalization Note** $\chi^*$ is `holevoCapacity`, an `EReal` supremum over finite ensembles; $\Psi\otimes\Phi$ is `tensorChannel Ψ Φ`. Entanglement breaking is the operational definition `IsEntanglementBreaking`. Index types are arbitrary finite types; inputs and outputs may differ.
--
--   Differences from the source:
--   - encoding: χ* = max over probability distributions p_i and density matrices ρ_i → holevoCapacity, the EReal supremum over finite ensembles (Fin n, every n) of density matrices; reason: the maximum is attained (p.1), so the value is the same
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: another quantum system Href in the definition of entanglement breaking → every reference ℂ^a (Fin a), a ∈ ℕ; reason: every finite-dimensional system is isomorphic to some ℂ^a
--   - encoding: Hilbert spaces of the channels → arbitrary finite index types, possibly empty; reason: with an empty input space there is no state and both sides are ⊥ (−∞); on nonempty spaces the statement is the source's
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (28), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_IsEntanglementBreaking
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorEBAdditivity_holevoCapacity

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (28), p.5: "we see that χ*(Ψ ⊗ Φ) ≤ χ*(Ψ) + χ*(Φ)", for an
arbitrary quantum channel `Ψ` and an entanglement breaking channel `Φ` (the hypotheses of
Theorem 2, p.4).

**Formalization Note.** Channels are `QAlgorithms.IsChannel` (finite normalized Kraus family,
equivalent to CPTP in finite dimension). `χ*` is `holevoCapacity`, the `EReal` supremum of the
Holevo quantity over all finite ensembles of density matrices; for `Ψ ⊗ Φ`
(`tensorChannel Ψ Φ`) the ensembles range over all densities on `A × B`, entangled ones
included. Entropy in bits. Input and output spaces are arbitrary finite types and may differ. -/
theorem eq_28 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    (hEB : IsEntanglementBreaking Φ) :
    holevoCapacity (tensorChannel Ψ Φ) ≤ holevoCapacity Ψ + holevoCapacity Φ := by sorry

end ShorEBAdditivity
