-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_4
-- name    : ShorEBAdditivity.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:55.033431+00:00
-- url     : https://prove2.me/theorems/c3ee5b93-b102-4fa9-91ed-ca3baa792ef4
-- title:
--   Eq. (4): superadditivity $\chi^*(\Psi\otimes\Phi) \ge \chi^*(\Psi) + \chi^*(\Phi)$
-- statement:
--   Let $\Psi : M_A\to M_{A'}$ and $\Phi : M_B\to M_{B'}$ be arbitrary quantum channels on finite-dimensional spaces. Then the Holevo–Schumacher–Westmoreland capacity is superadditive:
--
--   $$
--   \chi^*(\Psi\otimes\Phi) \ge \chi^*(\Psi) + \chi^*(\Phi).
--   $$
--
--   Superadditivity is what makes the regularized capacity $C(\Psi) = \lim_n \frac1n\chi^*(\Psi^{\otimes n})$ well defined, and it is "the opposite inequality" that, with (28), yields additivity in Theorem 2. No entanglement-breaking assumption is made.
--
--   **Formalization Note** $\chi^*$ is `holevoCapacity`, an `EReal` supremum over finite ensembles; $\Psi\otimes\Phi$ is `tensorChannel Ψ Φ`. Index types are arbitrary finite types. With an empty input space the corresponding capacity is $\bot$, and $\bot + x = \bot$.
--
--   Differences from the source:
--   - encoding: χ* = max over probability distributions p_i and density matrices ρ_i → holevoCapacity, the EReal supremum over finite ensembles (Fin n, every n) of density matrices; reason: the maximum is attained (p.1), so the value is the same
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
--   - encoding: quantum channel (CPTP map) → IsChannel (finite normalized Kraus family); reason: Choi–Kraus; same maps
--   - encoding: Hilbert spaces of the channels → arbitrary finite index types, possibly empty; reason: with an empty input space there is no state and the left side is ⊥ (−∞); on nonempty spaces the statement is the source's
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (4), p.1 (and p.5, "As the opposite inequality is easy")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorEBAdditivity_holevoCapacity

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (4), p.1: "χ* satisfies the superadditivity condition
χ*(Ψ ⊗ Φ) ≥ χ*(Ψ) + χ*(Φ)", for arbitrary quantum channels `Ψ` and `Φ` ("As the opposite
inequality is easy", p.5).

**Formalization Note.** Channels are `QAlgorithms.IsChannel` (finite normalized Kraus family,
equivalent to CPTP in finite dimension). `χ*` is `holevoCapacity`, the `EReal` supremum of the
Holevo quantity over all finite ensembles of density matrices; entropy in bits. No entanglement
breaking hypothesis. With an empty input type both `χ*(Ψ)` (or `χ*(Φ)`) and `χ*(Ψ ⊗ Φ)` are `⊥`,
and `⊥ + x = ⊥`. -/
theorem eq_4 {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    (Ψ : Superop A A') (Φ : Superop B B') (hΨ : IsChannel Ψ) (hΦ : IsChannel Φ) :
    holevoCapacity Ψ + holevoCapacity Φ ≤ holevoCapacity (tensorChannel Ψ Φ) := by sorry

end ShorEBAdditivity
