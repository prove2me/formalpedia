-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_21_3_1
-- name    : WildeQIT.Compression.Supplement.theorem_21_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:18:20.295853+00:00
-- url     : https://prove2.me/theorems/9831800b-940e-5d34-a969-6c5654861602
-- title:
--   Theorem 21.3.1 (Bennett–Shor–Smolin–Thapliyal): $C_{EA}(\mathcal N)=I(\mathcal N)$
-- statement:
--   The entanglement-assisted classical capacity of a quantum channel $\mathcal N_{A'\to B}$ equals its mutual information:
--
--   $$
--   C_{EA}(\mathcal N)=I(\mathcal N),\qquad I(\mathcal N)=\max_{\varphi_{AA'}}I(A;B)_\rho,\quad\rho_{AB}=\mathcal N_{A'\to B}(\varphi_{AA'}),
--   $$
--
--   where the maximum is over pure bipartite states $\varphi_{AA'}$ and $C_{EA}(\mathcal N)$ is the supremum of the rates achievable by entanglement-assisted classical codes (§21.1: shared entanglement of any form, maximal error probability).
--
--   It is the quantum analogue of Shannon's channel capacity theorem: a single-letter formula, with no regularization.
--
--   **Formalization Note** Achievable rates are the published `WildeQIT.EADamping.IsAchievableEARate` and $I(\mathcal N)$ the published `WildeQIT.EADamping.channelMutualInfo`. The equality $C_{EA}=I$ is stated as: $I(\mathcal N)$ is the least upper bound of the achievable rates.
--
--   Differences from the source:
--   - encoding: C_EA(N) = sup of achievable rates = I(N) → IsLUB {C | IsAchievableEARate N C} (channelMutualInfo N); reason: the exact meaning of "the supremum equals I(N)" in ℝ, without a junk value for unbounded sets
--   - encoding: Hilbert spaces of positive dimension (implicit) → `[Nonempty a]` on the input space; reason: a zero-dimensional space has no state, and the suprema defining the quantities would be empty; the hypothesis excludes only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 21.3.1, p. 593, eq. (21.28); §21.1, pp. 589–590

import Mathlib
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 21.3.1, p. 593.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 21.3.1 (Bennett–Shor–Smolin–Thapliyal)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 593, (21.28)): "The
entanglement-assisted classical capacity of a quantum channel is equal to the channel's mutual
information: `C_EA(N) = I(N)`, where the mutual information `I(N)` of a channel `N` is defined as
`I(N) ≡ max_{φ_AA′} I(A;B)_ρ`, `ρ_AB ≡ N_{A′→B}(φ_AA′)`, and `φ_AA′` is a pure bipartite state."

Formalization Note: `C_EA(N)` is the supremum of the rates of the published
`WildeQIT.EADamping.IsAchievableEARate` (§21.1, maximal error (21.8), shared pure entanglement of
any form and dimension); "`C_EA(N) = I(N)`" is stated as `IsLUB`: `I(N)` is the least upper bound
of the set of achievable rates. `I(N)` is the published `WildeQIT.EADamping.channelMutualInfo`
(supremum over pure inputs with a reference of any finite dimension). The input space is
nonempty (a Hilbert space of positive dimension). -/
theorem theorem_21_3_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    IsLUB {C : ℝ | WildeQIT.EADamping.IsAchievableEARate N C}
      (WildeQIT.EADamping.channelMutualInfo N) := by sorry

end WildeQIT.Compression.Supplement
