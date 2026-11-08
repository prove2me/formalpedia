-- Prove2me | Theorems.Thm_WildeQIT_Degradable_property_13_6_1
-- name    : WildeQIT.Degradable.property_13_6_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:58:43.959233+00:00
-- url     : https://prove2.me/theorems/23628ba6-74a8-4cce-a6ba-84496c466138
-- title:
--   Property 13.6.1 — the private information of a quantum channel is non-negative
-- statement:
--   **Property 13.6.1.** The private information $P(\mathcal N)$ of a quantum channel $\mathcal N$ is non-negative:
--
--   $$
--   P(\mathcal N)\ge0 .
--   $$
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: P(N) defined as a maximum over inputs → P(N) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: I(X;B) and I(X;E) evaluated on U^N(ρ_XA′) for an isometric extension U^N of N → the classical–quantum states Σ_x p(x)|x⟩⟨x| ⊗ N(ρ^x) and Σ_x p(x)|x⟩⟨x| ⊗ N^c(ρ^x), with N^c the complementary channel of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ (environment N.ι); reason: the XB and XE marginals of U^N(ρ_XA′) are these states, and any two isometric extensions differ by an isometry on the environment, which leaves I(X;E) unchanged
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Property 13.6.1, eq. (13.180), p. 416

import Definitions.Def_WildeQIT_Degradable_privateInfoChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Property 13.6.1, p. 416.
-/

namespace WildeQIT.Degradable

/-- **Property 13.6.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 416, eq. (13.180)). The private information `P(N)` of a quantum
channel `N` is non-negative: `P(N) ≥ 0`.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. `P(N)` is `privateInfoChannel N`, Definition 13.6.1. -/
theorem property_13_6_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    0 ≤ privateInfoChannel N := by sorry

end WildeQIT.Degradable
