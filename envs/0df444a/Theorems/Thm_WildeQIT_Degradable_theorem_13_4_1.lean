-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_4_1
-- name    : WildeQIT.Degradable.theorem_13_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:54.152466+00:00
-- url     : https://prove2.me/theorems/e4b3e038-d75a-4f35-bce4-c023aa39e850
-- title:
--   Theorem 13.4.1 — additivity of the mutual information of quantum channels: $I(\mathcal N\otimes\mathcal M)=I(\mathcal N)+I(\mathcal M)$
-- statement:
--   **Theorem 13.4.1 (Additivity of Quantum Mutual Information of Quantum Channels).** Let $\mathcal N$ and $\mathcal M$ be any quantum channels. Then the mutual information of the tensor-product channel $\mathcal N\otimes\mathcal M$ is the sum of their individual mutual informations:
--
--   $$
--   I(\mathcal N\otimes\mathcal M)=I(\mathcal N)+I(\mathcal M),
--   $$
--
--   where $I(\mathcal N)=\max_{\varphi_{AA'}}I(A;B)_{\mathcal N(\varphi)}$ and, for $\mathcal N\otimes\mathcal M$, the maximum ranges over pure states $\varphi_{AA_1'A_2'}$ that may be entangled across the two inputs.
--
--   Entangled inputs therefore never increase the mutual information of a pair of channels; this gives a single-letter formula for the entanglement-assisted classical capacity.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a, Nonempty c] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: I(·) defined as a maximum over inputs → I(·) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.4.1, eq. (13.122), p. 407

import Definitions.Def_WildeQIT_Degradable_mutualInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.4.1, p. 407.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.4.1 (Additivity of Quantum Mutual Information of Quantum Channels)**
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 407, eq. (13.122)). Let `N` and `M` be any quantum channels. Then the mutual
information of the tensor-product channel `N ⊗ M` is the sum of their individual mutual
informations: `I(N ⊗ M) = I(N) + I(M)`.

**Formalization Note.** The input spaces are nonzero (`Nonempty a`, `Nonempty c`), as every Hilbert space of the book is; without this, an empty `a` would make `N ⊗ M` have no input while `M` alone has one. `I(·)` is `mutualInfoChannel` (13.121), a supremum over pure inputs with
a reference of any finite dimension; `N ⊗ M` is `tensorChannel N M`. -/
theorem theorem_13_4_1 {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [Nonempty a] [Nonempty c]
    (N : QChannel a b) (M : QChannel c d) :
    mutualInfoChannel (tensorChannel N M) = mutualInfoChannel N + mutualInfoChannel M := by sorry

end WildeQIT.Degradable
