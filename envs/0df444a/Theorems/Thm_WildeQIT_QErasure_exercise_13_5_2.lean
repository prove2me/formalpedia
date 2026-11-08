-- Prove2me | Theorems.Thm_WildeQIT_QErasure_exercise_13_5_2
-- name    : WildeQIT.QErasure.exercise_13_5_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:37:50.214668+00:00
-- url     : https://prove2.me/theorems/495f55d6-a2f0-44b1-a8c1-5758efe96a3b
-- title:
--   Exercise 13.5.2: the erasure channel is degradable for $\varepsilon\in[0,1/2]$
-- statement:
--   Let $\mathcal N$ be the quantum erasure channel on a $d_A$-dimensional input ($d_A\ge1$) with erasure probability $\varepsilon\in[0,1/2]$. Then $\mathcal N$ is **degradable**: there is a channel $\mathcal D_{B\to E}$ with
--
--   $$
--   \mathcal N^c(\rho)=\mathcal D\big(\mathcal N(\rho)\big)\quad\text{for every input state }\rho .
--   $$
--
--   This is the fact the proof of Proposition 24.7.1 uses to reduce the quantum capacity of the erasure channel for $\varepsilon\le 1/2$ to its single-letter coherent information.
--
--   **Formalization Note** The exercise asks to find the degrading channel; the statement asserts it exists. The complementary channel is that of the canonical isometric extension of the Kraus form of the erasure channel.
--
--   Differences from the source:
--   - reading: "Find the channel that degrades this one, reproducing the channel from input to environment" → IsDegradable (erasureChannel a ε h0 h1): existence of a degrading channel; reason: the exercise asks for a witness of Definition 13.5.2, and degradability is what the proof of Proposition 24.7.1 cites it for
--   - encoding: an input system of dimension d_A → a nonempty finite index type a with d_A = |a|; reason: a Hilbert space carrying a state has dimension at least one
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Exercise 13.5.2, p. 414; used in the proof of Proposition 24.7.1, p. 677

import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Definitions.Def_WildeQIT_QErasure_erasureChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Exercise 13.5.2, p. 414
(used in the proof of Proposition 24.7.1, p. 677).
-/

namespace WildeQIT.QErasure

/-- **Exercise 13.5.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 414): "Consider the quantum erasure channel where the erasure parameter `ε ∈ [0, 1/2]`. Find the
channel that degrades this one, reproducing the channel from input to environment." That is, for
`ε ∈ [0, 1/2]` the quantum erasure channel is degradable (Definition 13.5.2), as used in the proof of
Proposition 24.7.1, p. 677.

**Formalization Note.** The input system is any nonempty finite type `a` (`d_A = |a| ≥ 1`); the complementary channel is the
one of the canonical isometric extension of the Kraus form of `erasureChannel`. -/
theorem exercise_13_5_2 (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hε : ε ≤ 1 / 2) :
    WildeQIT.Degradable.IsDegradable (erasureChannel a ε h0 h1) := by sorry

end WildeQIT.QErasure
