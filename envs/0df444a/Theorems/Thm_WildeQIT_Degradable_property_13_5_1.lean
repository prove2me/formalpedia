-- Prove2me | Theorems.Thm_WildeQIT_Degradable_property_13_5_1
-- name    : WildeQIT.Degradable.property_13_5_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:58:45.588348+00:00
-- url     : https://prove2.me/theorems/e51c127b-4c2a-4c3c-a722-c45da53733f4
-- title:
--   Property 13.5.1 — the coherent information of a quantum channel is non-negative
-- statement:
--   **Property 13.5.1 (Non-Negativity of Channel Coherent Information).** The coherent information $Q(\mathcal N)$ of a quantum channel $\mathcal N$ is non-negative:
--
--   $$
--   Q(\mathcal N)\ge0 .
--   $$
--
--   This holds although the coherent information $I(A\rangle B)_\rho$ of a given state can be negative.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: Q(N) defined as a maximum over inputs → Q(N) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 13.5.1, eq. (13.151), p. 411

import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 13.5.1, p. 411.
-/

namespace WildeQIT.Degradable

/-- **Property 13.5.1 (Non-Negativity of Channel Coherent Information)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 411,
eq. (13.151)). The coherent information `Q(N)` of a quantum channel `N` is non-negative:
`Q(N) ≥ 0`.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. `Q(N)` is `coherentInfoChannel N`, Definition 13.5.1. -/
theorem property_13_5_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    0 ≤ coherentInfoChannel N := by sorry

end WildeQIT.Degradable
