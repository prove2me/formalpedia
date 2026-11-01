-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_6_3
-- name    : WildeQIT.Degradable.theorem_13_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:56.867806+00:00
-- url     : https://prove2.me/theorems/b6f7ae34-a68d-4030-b898-84ccac555427
-- title:
--   Theorem 13.6.3 — additivity of private information for degradable channels: $P(\mathcal N\otimes\mathcal M)=P(\mathcal N)+P(\mathcal M)=Q(\mathcal N\otimes\mathcal M)=Q(\mathcal N)+Q(\mathcal M)$
-- statement:
--   **Theorem 13.6.3 (Additivity for Degradable Quantum Channels).** Let $\mathcal N$ and $\mathcal M$ be any quantum channels that are degradable. Then the private information of the tensor-product channel $\mathcal N\otimes\mathcal M$ is the sum of their individual private informations:
--
--   $$
--   P(\mathcal N\otimes\mathcal M)=P(\mathcal N)+P(\mathcal M).
--   $$
--
--   Furthermore, it holds that
--
--   $$
--   P(\mathcal N\otimes\mathcal M)=Q(\mathcal N\otimes\mathcal M)=Q(\mathcal N)+Q(\mathcal M).
--   $$
--
--   Here $P$ and $Q$ are the private and coherent information of a channel (Definitions 13.6.1 and 13.5.1); for $\mathcal N\otimes\mathcal M$ the inputs may be correlated or entangled across the two channel uses, and its environment is the joint environment $E_1E_2$. Correlated inputs therefore cannot enhance the private information of degradable channels.
--
--   The statement consists of three equalities: $P(\mathcal N\otimes\mathcal M)=P(\mathcal N)+P(\mathcal M)$, $P(\mathcal N\otimes\mathcal M)=Q(\mathcal N\otimes\mathcal M)$, and $Q(\mathcal N\otimes\mathcal M)=Q(\mathcal N)+Q(\mathcal M)$.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a, Nonempty c] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: P(·) and Q(·) defined as a maximum over inputs → P(·) and Q(·) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: degradable: D ∘ N = N^c for a channel N^c complementary to N → IsDegradable: a Kraus channel D from B to the environment of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ with D(N(ρ)) = N^c(ρ) for every density operator ρ; reason: two complementary channels differ by an isometry (or partial isometry) on the environment, so degradability does not depend on the choice
--   - encoding: I(X;B) and I(X;E) evaluated on U^N(ρ_XA′) for an isometric extension U^N of N → the classical–quantum states Σ_x p(x)|x⟩⟨x| ⊗ N(ρ^x) and Σ_x p(x)|x⟩⟨x| ⊗ N^c(ρ^x), with N^c the complementary channel of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ (environment N.ι); reason: the XB and XE marginals of U^N(ρ_XA′) are these states, and any two isometric extensions differ by an isometry on the environment, which leaves I(X;E) unchanged
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.6.3, eqs. (13.205)–(13.206), p. 419

import Definitions.Def_WildeQIT_Degradable_privateInfoChannel
import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Definitions.Def_WildeQIT_Degradable_tensorChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.6.3, p. 419.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.6.3 (Additivity for Degradable Quantum Channels)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 419,
eqs. (13.205)–(13.206)). Let `N` and `M` be any quantum channels that are degradable. Then the
private information of the tensor-product channel `N ⊗ M` is the sum of their individual private
informations: `P(N ⊗ M) = P(N) + P(M)`. Furthermore, it holds that
`P(N ⊗ M) = Q(N ⊗ M) = Q(N) + Q(M)`.

**Formalization Note.** The input spaces are nonzero (`Nonempty a`, `Nonempty c`), as every Hilbert space of the book is; without this, an empty `a` would make `N ⊗ M` have no input while `M` alone has one. The conclusion is the conjunction of the three equalities
`P(N ⊗ M) = P(N) + P(M)`, `P(N ⊗ M) = Q(N ⊗ M)` and `Q(N ⊗ M) = Q(N) + Q(M)` printed in
(13.205)–(13.206). `N ⊗ M` is `tensorChannel N M` with the joint environment `E₁E₂`;
degradability is Definition 13.5.2. -/
theorem theorem_13_6_3 {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [Nonempty a] [Nonempty c]
    (N : QChannel a b) (M : QChannel c d) (hN : IsDegradable N) (hM : IsDegradable M) :
    privateInfoChannel (tensorChannel N M) = privateInfoChannel N + privateInfoChannel M ∧
      privateInfoChannel (tensorChannel N M) = coherentInfoChannel (tensorChannel N M) ∧
      coherentInfoChannel (tensorChannel N M) =
        coherentInfoChannel N + coherentInfoChannel M := by sorry

end WildeQIT.Degradable
