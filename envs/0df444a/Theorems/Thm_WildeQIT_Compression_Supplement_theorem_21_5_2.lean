-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_21_5_2
-- name    : WildeQIT.Compression.Supplement.theorem_21_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:19:15.418929+00:00
-- url     : https://prove2.me/theorems/d0e3ca23-d752-4c0d-bcdc-15609dd08981
-- title:
--   Theorem 21.5.2 (Quantum Feedback Does Not Increase EAC Capacity): $\sup\{C\text{ achievable with quantum feedback}\}=I(\mathcal N)$
-- statement:
--   Let $\mathcal N$ be a quantum channel. The classical capacity of $\mathcal N$ assisted by a noiseless quantum feedback channel of unbounded dimension from receiver to sender equals the entanglement-assisted classical capacity:
--
--   $$
--   \sup\{C : C\text{ is achievable for }\mathcal N\text{ with quantum feedback}\}=I(\mathcal N)=\max_{\varphi_{AA'}}I(A;B).
--   $$
--
--   The protocols are the most general ones of Figure 21.4: rounds of encoding by Alice, a channel use, decoding by Bob and quantum feedback, with a uniformly distributed message and error $\Pr\{M'\neq M\}\le\varepsilon$.
--
--   Together with Theorem 21.3.1 this places the entanglement-assisted capacity as the quantum analogue of Shannon's result that feedback does not increase capacity.
--
--   **Formalization Note** Achievable rates are `IsAchievableQFeedbackRate`; $I(\mathcal N)$ is the published `WildeQIT.EADamping.channelMutualInfo`. The supremum is stated as a least upper bound.
--
--   Differences from the source:
--   - encoding: sup {C | C achievable with quantum feedback} = I(N) → IsLUB {C | IsAchievableQFeedbackRate N C} (channelMutualInfo N); reason: the exact meaning of the supremum in ℝ
--   - encoding: memories and feedback systems of arbitrary, possibly round-dependent, finite dimension → one finite dimension per kind of system; reason: a protocol with round-dependent dimensions embeds isometrically into one with the maximal dimension, so the set of achievable rates is the same
--   - encoding: Hilbert spaces of positive dimension (implicit) → `[Nonempty a]` on the input space; reason: a zero-dimensional space has no state, and the suprema defining the quantities would be empty; the hypothesis excludes only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 21.5.2, p. 605, eq. (21.124); proof and Figure 21.4, pp. 605–606

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_IsAchievableQFeedbackRate
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 21.5.2, p. 605.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 21.5.2 (Quantum Feedback Does Not Increase EAC Capacity)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 605,
(21.124)): "The classical capacity of a quantum channel assisted by a quantum feedback channel is
equal to that channel's entanglement-assisted classical capacity:
`sup {C | C is achievable for N with quantum feedback} = I(N)`, where `I(N)` is defined in
(21.112)", `I(N) = max_{φ_AA′} I(A;B)`.

Formalization Note: rates achievable with quantum feedback are `IsAchievableQFeedbackRate`
(the most general protocol of Figure 21.4, p. 606, with feedback systems of arbitrary finite
dimension, a uniform message and error `Pr{M′ ≠ M} ≤ ε`; no prior shared entanglement). The
supremum is stated as `IsLUB`. `I(N)` is the published `WildeQIT.EADamping.channelMutualInfo`.
The input space is nonempty. -/
theorem theorem_21_5_2 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    IsLUB {C : ℝ | IsAchievableQFeedbackRate N C} (WildeQIT.EADamping.channelMutualInfo N) := by sorry

end WildeQIT.Compression.Supplement
