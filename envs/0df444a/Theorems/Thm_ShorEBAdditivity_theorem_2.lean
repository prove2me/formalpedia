-- Prove2me | Theorems.Thm_ShorEBAdditivity_theorem_2
-- name    : ShorEBAdditivity.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:56.748653+00:00
-- url     : https://prove2.me/theorems/90f4bf7a-08e6-430a-851f-89727623bad1
-- title:
--   Theorem 2: $\chi^*(\Psi\otimes\Phi) = \chi^*(\Psi) + \chi^*(\Phi)$ for any channel $\Psi$ and entanglement-breaking $\Phi$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ be an arbitrary quantum channel and $\Phi : M_B\to M_{B'}$ an entanglement-breaking quantum channel, all spaces finite-dimensional. Then the Holevo–Schumacher–Westmoreland capacity is additive on this pair:
--
--   $$
--   \chi^*(\Psi\otimes\Phi) = \chi^*(\Psi) + \chi^*(\Phi),
--   $$
--
--   where $\chi^*(\Theta) = \max_{p_i,\rho_i} H(\Theta(\sum_i p_i\rho_i)) - \sum_i p_i H(\Theta(\rho_i))$, the maximum running over finite probability distributions $p_i$ and density matrices $\rho_i$ on the input space of $\Theta$, and $H$ is the von Neumann entropy. For $\Psi\otimes\Phi$ the inputs $\rho_i$ range over all density matrices on $\mathcal H_A\otimes\mathcal H_B$, entangled ones included.
--
--   This is Shor's main theorem: entangled inputs across one use of $\Psi$ and one use of an entanglement-breaking channel do not increase the classical capacity, and by induction $\chi^*(\Phi^{\otimes n}) = n\chi^*(\Phi)$, so $\chi^*(\Phi)$ is the classical capacity of an entanglement-breaking channel.
--
--   **Formalization Note** $\chi^*$ is `holevoCapacity`, an `EReal` supremum over finite ensembles (`IsEnsemble`); $\Psi\otimes\Phi$ is `tensorChannel Ψ Φ`. Channels are `IsChannel` (finite normalized Kraus families); entanglement breaking is the operational definition `IsEntanglementBreaking`. Index types are arbitrary finite types, inputs and outputs may differ, and none is assumed nonempty. Both inequalities are asserted.
--
--   Differences from the source:
--   - encoding: χ* = max over probability distributions p_i and density matrices ρ_i → holevoCapacity, the EReal supremum over finite ensembles (Fin n, every n) of density matrices; reason: the maximum is attained (p.1), so the value is the same
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: another quantum system Href in the definition of entanglement breaking → every reference ℂ^a (Fin a), a ∈ ℕ; reason: every finite-dimensional system is isomorphic to some ℂ^a
--   - encoding: Hilbert spaces of the channels → arbitrary finite index types, possibly empty; reason: with an empty input space there is no state and both sides are ⊥ (−∞); on nonempty spaces the statement is the source's
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, Theorem 2, eq. (16), p.4 (χ* as in eq. (15), p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_IsEntanglementBreaking
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorEBAdditivity_holevoCapacity

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, Theorem 2, eq. (16), p.4: "For an arbitrary quantum channel Ψ, and an
entanglement breaking channel Φ, χ*(Ψ ⊗ Φ) = χ*(Ψ) + χ*(Φ)."

**Formalization Note.** `Ψ : M_A → M_{A'}` and `Φ : M_B → M_{B'}` are channels
(`QAlgorithms.IsChannel`: a finite normalized Kraus family, equivalent to CPTP in finite
dimension) between arbitrary finite-dimensional spaces; input and output may differ, and no space
is assumed nonempty. `Φ` is entanglement breaking in the paper's operational sense
(`IsEntanglementBreaking`: separable output for every finite reference and every joint input
density). `χ*` is `holevoCapacity`: the `EReal` supremum of
`H(Ψ(Σ p_i ρ_i)) − Σ p_i H(Ψ(ρ_i))` over all finite ensembles of (mixed) density matrices, with
`H` the von Neumann entropy in bits; the paper's maximum is attained (p.1), so the supremum is the
same number. For `Ψ ⊗ Φ` (`tensorChannel Ψ Φ`) the ensembles range over all densities on
`A × B`, entangled ones included. Both inequalities are asserted. -/
theorem theorem_2 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ)
    (hEB : IsEntanglementBreaking Φ) :
    holevoCapacity (tensorChannel Ψ Φ) = holevoCapacity Ψ + holevoCapacity Φ := by sorry

end ShorEBAdditivity
