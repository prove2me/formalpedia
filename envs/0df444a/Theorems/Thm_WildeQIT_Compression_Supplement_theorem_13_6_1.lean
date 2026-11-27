-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_13_6_1
-- name    : WildeQIT.Compression.Supplement.theorem_13_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:15:53.927506+00:00
-- url     : https://prove2.me/theorems/0c777b4c-5123-511c-850d-017b420decc8
-- title:
--   Theorem 13.6.1: $Q(\mathcal N)\le P(\mathcal N)$
-- statement:
--   For every quantum channel $\mathcal N$, the private information is never smaller than the coherent information:
--
--   $$
--   Q(\mathcal N)\le P(\mathcal N),
--   $$
--
--   where $Q(\mathcal N)=\max_{\varphi_{AA'}}I(A\rangle B)$ is the coherent information of the channel (Definition 13.5.1) and $P(\mathcal N)=\max_{\rho_{XA'}}[I(X;B)-I(X;E)]$ its private information (Definition 13.6.1).
--
--   It reflects that quantum communication implies private communication.
--
--   **Formalization Note** $Q$ and $P$ are the published `WildeQIT.Degradable.coherentInfoChannel` and `WildeQIT.Degradable.privateInfoChannel`.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.6.1, p. 417, eq. (13.183)

import Mathlib
import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_privateInfoChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.6.1, p. 417.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 13.6.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 417, (13.183)): "The private information `P(N)` of any quantum
channel `N` is never smaller than its coherent information `Q(N)`: `Q(N) ≤ P(N)`."

Formalization Note: `Q(N)` is the published `WildeQIT.Degradable.coherentInfoChannel`
(Definition 13.5.1) and `P(N)` the published `WildeQIT.Degradable.privateInfoChannel`
(Definition 13.6.1), both suprema of bounded sets; every channel in Kraus form. -/
theorem theorem_13_6_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QChannel a b) :
    WildeQIT.Degradable.coherentInfoChannel N ≤ WildeQIT.Degradable.privateInfoChannel N := by sorry

end WildeQIT.Compression.Supplement
