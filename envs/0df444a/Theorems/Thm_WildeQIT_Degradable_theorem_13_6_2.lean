-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_6_2
-- name    : WildeQIT.Degradable.theorem_13_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:59:04.48307+00:00
-- url     : https://prove2.me/theorems/f1b90e9b-bb21-401c-ab88-e5761e2e1890
-- title:
--   Theorem 13.6.2 — for a degradable channel, private information equals coherent information
-- statement:
--   **Theorem 13.6.2.** Suppose that a quantum channel $\mathcal N$ is degradable. Then its private information $P(\mathcal N)$ is equal to its coherent information $Q(\mathcal N)$:
--
--   $$
--   P(\mathcal N)=Q(\mathcal N).
--   $$
--
--   For any channel $Q(\mathcal N)\le P(\mathcal N)$ (Theorem 13.6.1); degradability gives the reverse inequality.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: P(N) and Q(N) defined as a maximum over inputs → P(N) and Q(N) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: degradable: D ∘ N = N^c for a channel N^c complementary to N → IsDegradable: a Kraus channel D from B to the environment of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ with D(N(ρ)) = N^c(ρ) for every density operator ρ; reason: two complementary channels differ by an isometry (or partial isometry) on the environment, so degradability does not depend on the choice
--   - encoding: I(X;B) and I(X;E) evaluated on U^N(ρ_XA′) for an isometric extension U^N of N → the classical–quantum states Σ_x p(x)|x⟩⟨x| ⊗ N(ρ^x) and Σ_x p(x)|x⟩⟨x| ⊗ N^c(ρ^x), with N^c the complementary channel of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ (environment N.ι); reason: the XB and XE marginals of U^N(ρ_XA′) are these states, and any two isometric extensions differ by an isometry on the environment, which leaves I(X;E) unchanged
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.6.2, eq. (13.193), p. 417

import Definitions.Def_WildeQIT_Degradable_privateInfoChannel
import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_IsDegradable

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.6.2, p. 417.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.6.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 417, eq. (13.193)). Suppose that a quantum channel `N` is
degradable. Then its private information `P(N)` is equal to its coherent information `Q(N)`:
`P(N) = Q(N)`.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. Degradability is Definition 13.5.2 (`IsDegradable`); `P` and `Q` are
Definitions 13.6.1 and 13.5.1. -/
theorem theorem_13_6_2 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) (hN : IsDegradable N) :
    privateInfoChannel N = coherentInfoChannel N := by sorry

end WildeQIT.Degradable
