-- Prove2me | Theorems.Thm_WildeQIT_QErasure_coherentInfoChannel_erasure
-- name    : WildeQIT.QErasure.coherentInfoChannel_erasure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:19.054618+00:00
-- url     : https://prove2.me/theorems/ed62aa5d-9875-4dc7-b008-9dace5804347
-- title:
--   Eq. (24.131): $Q(\mathcal N)=(1-2\varepsilon)\log d_A$ for the erasure channel, $\varepsilon\le1/2$
-- statement:
--   Let $\mathcal N$ be the quantum erasure channel on a $d_A$-dimensional input ($d_A\ge1$) with erasure probability $\varepsilon\in[0,1/2]$. Then its coherent information is
--
--   $$
--   Q(\mathcal N)=(1-2\varepsilon)\log d_A .
--   $$
--
--   The upper bound is (24.131), from $H(A)_\varphi\le\log d_A$; the maximally entangled state $\Phi_{AA'}$ attains it because $H(A)_\Phi=\log d_A$.
--
--   **Formalization Note** Logarithms are base 2; $Q(\mathcal N)$ is the supremum over pure inputs with a reference of any finite dimension.
--
--   Differences from the source:
--   - reading: "≤ (1 − 2ε) log dA (24.131) … the maximally entangled state ΦAA′ achieves …" → coherentInfoChannel (erasureChannel a ε h0 h1) = (1 − 2ε) logb 2 |a|; reason: the bound and its attainment together are the equality
--   - encoding: an input system of dimension d_A → a nonempty finite index type a with d_A = |a|; reason: a Hilbert space carrying a state has dimension at least one
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Proposition 24.7.1, (24.131), p. 678

import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_QErasure_erasureChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Proposition 24.7.1,
p. 678, eq. (24.131) and the paragraph after it.
-/

namespace WildeQIT.QErasure

/-- **Eq. (24.131) and the maximally entangled input** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 678): for `ε ∈ [0, 1/2]` the coherent information of the quantum
erasure channel is at most `(1 − 2ε) log d_A` (24.131), and "the maximally entangled state `Φ_{AA′}`
achieves" it "because `H(A)_Φ = log d_A`". Hence `Q(N) = (1 − 2ε) log d_A` (Definition 13.5.1).

**Formalization Note.** The input system is a nonempty finite type `a`, `d_A = |a|`; logarithms are
base 2. -/
theorem coherentInfoChannel_erasure (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hε : ε ≤ 1 / 2) :
    WildeQIT.Degradable.coherentInfoChannel (erasureChannel a ε h0 h1) = (1 - 2 * ε) * Real.logb 2 (Fintype.card a) := by sorry

end WildeQIT.QErasure
