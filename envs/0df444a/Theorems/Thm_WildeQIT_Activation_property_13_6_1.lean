-- Prove2me | Theorems.Thm_WildeQIT_Activation_property_13_6_1
-- name    : WildeQIT.Activation.property_13_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:13:57.460985+00:00
-- url     : https://prove2.me/theorems/7dbc8b46-4fd9-414b-ae66-fa9b591a7931
-- title:
--   Property 13.6.1 — the private information of a quantum channel is non-negative
-- statement:
--   **Property 13.6.1.** The private information $P(\mathcal N)$ of a quantum channel $\mathcal N$ is non-negative:
--
--   $$
--   P(\mathcal N)\ge0 .
--   $$
--
--   In Theorem 24.8.1 this makes the lower bound $Q(\mathcal N_1\otimes\mathcal N_2)\ge P(\mathcal N_2)/2$ a statement about a non-negative quantity.
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types, the book's setting; entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; $P(\mathcal N)$ is `privateInfoChannel`.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: P(N) defined as a maximum over inputs → P(N) defined as a real supremum over ensembles with alphabet Fin k, k arbitrary; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 13.6.1, eq. (13.180), p. 416

import Definitions.Def_WildeQIT_Activation_privateInfoChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 13.6.1, p. 416, eq. (13.180).
-/

namespace WildeQIT.Activation

/-- **Property 13.6.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 416, eq. (13.180)). The private information `P(N)` of a quantum
channel `N` is non-negative: `P(N) ≥ 0`.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the
book is. `P(N)` is `privateInfoChannel N`, Definition 13.6.1, a real supremum over all
ensembles with a finite alphabet of any size. -/
theorem property_13_6_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    0 ≤ privateInfoChannel N := by sorry

end WildeQIT.Activation
