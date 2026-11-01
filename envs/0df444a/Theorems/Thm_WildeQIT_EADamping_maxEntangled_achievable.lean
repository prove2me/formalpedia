-- Prove2me | Theorems.Thm_WildeQIT_EADamping_maxEntangled_achievable
-- name    : WildeQIT.EADamping.maxEntangled_achievable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:39:54.318476+00:00
-- url     : https://prove2.me/theorems/a8e7bf60-bf40-4e4e-89fc-aa6dbcd934ba
-- title:
--   Corollary 21.2.1: $I(A;B)_\sigma$ for $\sigma_{AB}=\mathcal N_{A'\to B}(\Phi_{AA'})$ is an achievable entanglement-assisted rate
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel on finite-dimensional systems, let $\Phi_{AA'}$ be the maximally entangled state on two copies of the input system, and let $\sigma_{AB}\equiv\mathcal N_{A'\to B}(\Phi_{AA'})$. Then the quantum mutual information
--
--   $$
--   I(A;B)_\sigma
--   $$
--
--   is an achievable rate for entanglement-assisted classical communication over $\mathcal N_{A'\to B}$: for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an entanglement-assisted classical code with at least $2^{n(I(A;B)_\sigma-\delta)}$ messages and maximal error probability at most $\varepsilon$.
--
--   It is the super-dense-coding lower bound on the entanglement-assisted capacity; for the amplitude damping channel it is strictly below the capacity.
--
--   **Formalization Note** Finite dimensions, logarithms base 2. $\Phi_{AA'}$ is the published `ObliviousRSP.maxEnt a`, the projector $|\Phi\rangle\langle\Phi|$ with entry $1/|a|$ at $((i,i),(j,j))$ and $0$ elsewhere, with the reference $A$ a copy of the input type `a`; achievability is `IsAchievableEARate` (Section 21.1).
--
--   Differences from the source:
--   - encoding: the input system is a Hilbert space (dimension at least one) → `[Nonempty a]`; reason: for an empty input type no code exists, so the statement would be false on an instance outside the book
--   - reading: an $(n,C-\delta,\varepsilon)$ code, rate $\frac1n\log|\mathcal M|=C-\delta$ → at least $2^{n(C-\delta)}$ messages; reason: the book's rate is generally not of the form $\frac1n\log k$, and "at least" is the standard reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.2, Corollary 21.2.1, p. 591; §21.1, p. 590

import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
import Definitions.Def_WildeQIT_EADamping_idTensorApply
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_ObliviousRSP_maxEnt

namespace WildeQIT.EADamping

open WildeQIT

/-- **Corollary 21.2.1.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 21.2.1, p. 591:
the quantum mutual information `I(A; B)_σ` of the state `σ_{AB} ≡ N_{A′→B}(Φ_{AA′})` is an
achievable rate for entanglement-assisted classical communication over a quantum channel
`N_{A′→B}`.

**Formalization Note.** Finite dimensions, bits. `Φ_{AA′}` is the published `ObliviousRSP.maxEnt a` (`|Φ⟩⟨Φ|`, entry `1/|a|` at `((i, i), (j, j))`), with the reference
`A` a copy of the input space. The input space is nonempty (a quantum system has dimension at least
one; with an empty input no code exists). Achievability is `IsAchievableEARate` (§21.1). -/
theorem maxEntangled_achievable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] [Nonempty a] (N : QChannel a b) :
    IsAchievableEARate N (DattaDiscord.mutualInfo (idTensorApply N (ObliviousRSP.maxEnt a))) := by sorry

end WildeQIT.EADamping
