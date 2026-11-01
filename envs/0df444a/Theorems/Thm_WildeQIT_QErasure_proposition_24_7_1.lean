-- Prove2me | Theorems.Thm_WildeQIT_QErasure_proposition_24_7_1
-- name    : WildeQIT.QErasure.proposition_24_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:40:47.155984+00:00
-- url     : https://prove2.me/theorems/aa2c51a1-dcfe-45be-99cb-df7e7ae44f7e
-- title:
--   Proposition 24.7.1: the quantum capacity of the erasure channel is $(1-2\varepsilon)\log d_A$ for $\varepsilon\le1/2$, zero otherwise
-- statement:
--   Let $\mathcal N$ be the quantum erasure channel on an input system of dimension $d_A\ge1$ with erasure probability $\varepsilon\in[0,1]$. Its quantum capacity is
--
--   $$
--   C_Q(\mathcal N)=\begin{cases}(1-2\varepsilon)\log d_A, & \varepsilon\in[0,1/2],\\[2pt] 0, & \varepsilon\in(1/2,1].\end{cases}
--   $$
--
--   Here $C_Q$ is the supremum of all rates achievable by codes $(\mathcal E,\mathcal D)$ that transmit **every** state $|\phi\rangle_{RA_1}$ with $\frac12\|\phi_{RA_1}-\omega_{RB_1}\|_1\le\varepsilon'$, for every $\varepsilon'\in(0,1)$ and all large block lengths. The two branches agree at $\varepsilon=1/2$.
--
--   The erasure channel is one of the few channels whose quantum capacity is known exactly; the result shows that half of the erasure probability is lost to the environment, and that the capacity vanishes as soon as Eve receives the state at least as often as Bob.
--
--   **Formalization Note** The input is a nonempty finite type `a` with $d_A=|a|$, logarithms are base 2, and the capacity is the supremum in `EReal` of the achievable rates (no junk value on an empty or unbounded set).
--
--   Differences from the source:
--   - encoding: an input system of dimension d_A → a nonempty finite index type a with d_A = |a|; reason: a Hilbert space carrying a state has dimension at least one
--   - encoding: C_Q(N), the supremum of all achievable rates → quantumCapacity: sSup in EReal of the achievable rates; reason: the least upper bound in the extended reals; equal to the real supremum when the set is nonempty and bounded
--   - reading: an (n, Q − δ, ε) code, of rate Q − δ = (1/n) log dim(H_A1) → a code with dim(H_A1) = m ≥ 1 and n(Q − δ) ≤ log₂ m; reason: a rate of exactly Q − δ is in general not the logarithm of an integer; a code of larger rate restricts to every smaller dimension
--   - encoding: "equal to zero otherwise", with ε ∈ [0, 1] standing in (24.121) → if ε ≤ 1/2 then (1 − 2ε) log₂ |a| else 0, with hypotheses 0 ≤ ε ≤ 1; reason: "otherwise" is ε ∈ (1/2, 1]; log is base 2 in the book
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 24.7.1, p. 677; operational definitions §24.1, (24.1)–(24.3), pp. 658–659

import Definitions.Def_WildeQIT_QErasure_quantumCapacity
import Definitions.Def_WildeQIT_QErasure_erasureChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Proposition 24.7.1, p. 677.
-/

namespace WildeQIT.QErasure

/-- **Proposition 24.7.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 677). "Let `d_A` be the dimension of the input system for the quantum erasure channel. The quantum
capacity of a quantum erasure channel with erasure probability `ε` is equal to `(1 − 2ε) log d_A`
when `ε ∈ [0, 1/2]` and it is equal to zero otherwise."

**Formalization Note.** The input system is indexed by a nonempty finite type `a`, `d_A = |a|`;
`ε ∈ [0, 1]` is standing in (24.121), so "otherwise" is `ε ∈ (1/2, 1]`. The capacity is the
supremum in `EReal` of the achievable rates of §24.1 (codes good for every input state
`|ϕ⟩_{RA₁}`), and the logarithm is base 2. -/
theorem proposition_24_7_1 (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    quantumCapacity (erasureChannel a ε h0 h1) =
      ((if ε ≤ 1 / 2 then (1 - 2 * ε) * Real.logb 2 (Fintype.card a) else 0 : ℝ) : EReal) := by sorry

end WildeQIT.QErasure
