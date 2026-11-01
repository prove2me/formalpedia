-- Prove2me | Theorems.Thm_WildeQIT_QErasure_exercise_13_5_6
-- name    : WildeQIT.QErasure.exercise_13_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:20.841334+00:00
-- url     : https://prove2.me/theorems/45f542a3-4b8f-4bff-b6c6-fca6dfaf6b77
-- title:
--   Exercise 13.5.6: an antidegradable channel has zero coherent information
-- statement:
--   Let $\mathcal N_{A'\to B}$ be an antidegradable quantum channel. Then its coherent information vanishes:
--
--   $$
--   Q(\mathcal N)=\max_{\varphi_{AA'}} I(A\rangle B)_{\mathcal N(\varphi)}=0 .
--   $$
--
--   Applied to $\mathcal N^{\otimes n}$, this gives the converse half of Proposition 24.7.1.
--
--   **Formalization Note** The maximum is the supremum over pure inputs with a reference of any finite dimension.
--
--   Differences from the source:
--   - encoding: an input Hilbert space → a nonempty finite index type a; reason: a Hilbert space carrying a state has dimension at least one
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Exercise 13.5.6, p. 414

import Definitions.Def_WildeQIT_QErasure_IsAntidegradable
import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Exercise 13.5.6, p. 414.
-/

namespace WildeQIT.QErasure

/-- **Exercise 13.5.6** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 414): "Prove that the coherent information of an antidegradable channel is equal to zero."
`Q(N) = 0` for every antidegradable channel `N` (Definitions 13.5.1 and 13.5.3).

**Formalization Note.** The input space is nonempty, as every Hilbert space of the book is. -/
theorem exercise_13_5_6 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) (hN : IsAntidegradable N) :
    WildeQIT.Degradable.coherentInfoChannel N = 0 := by sorry

end WildeQIT.QErasure
