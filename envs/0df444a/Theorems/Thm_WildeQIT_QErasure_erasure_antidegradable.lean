-- Prove2me | Theorems.Thm_WildeQIT_QErasure_erasure_antidegradable
-- name    : WildeQIT.QErasure.erasure_antidegradable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:13.583999+00:00
-- url     : https://prove2.me/theorems/82bb73b5-5e75-495c-a0bc-84eadc5da3b8
-- title:
--   Proposition 24.7.1 (proof, p. 677): the erasure channel is antidegradable for $\varepsilon\in[1/2,1]$
-- statement:
--   Let $\mathcal N$ be the quantum erasure channel on a $d_A$-dimensional input ($d_A\ge1$) with erasure probability $\varepsilon\in[1/2,1]$. Then $\mathcal N$ is **antidegradable**: there is a channel $\mathcal D_{E\to B}$ with
--
--   $$
--   \mathcal D\big(\mathcal N^c(\rho)\big)=\mathcal N(\rho)\quad\text{for every input state }\rho .
--   $$
--
--   Together with the vanishing coherent information of antidegradable channels, this gives the zero branch of Proposition 24.7.1.
--
--   **Formalization Note** The complementary channel is that of the canonical isometric extension of the Kraus form of the erasure channel.
--
--   Differences from the source:
--   - encoding: an input system of dimension d_A → a nonempty finite index type a with d_A = |a|; reason: a Hilbert space carrying a state has dimension at least one
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Proposition 24.7.1, p. 677

import Definitions.Def_WildeQIT_QErasure_IsAntidegradable
import Definitions.Def_WildeQIT_QErasure_erasureChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Proposition 24.7.1,
p. 677, first sentence.
-/

namespace WildeQIT.QErasure

/-- **Proof of Proposition 24.7.1, p. 677** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8): "The quantum erasure channel is antidegradable for `ε ∈ [1/2, 1]`."
(Definition 13.5.3.)

**Formalization Note.** The input system is any nonempty finite type `a` (`d_A = |a| ≥ 1`); the complementary channel is the
one of the canonical isometric extension of the Kraus form of `erasureChannel`. -/
theorem erasure_antidegradable (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hε : 1 / 2 ≤ ε) :
    IsAntidegradable (erasureChannel a ε h0 h1) := by sorry

end WildeQIT.QErasure
