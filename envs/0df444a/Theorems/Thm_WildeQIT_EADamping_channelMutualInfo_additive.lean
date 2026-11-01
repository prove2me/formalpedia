-- Prove2me | Theorems.Thm_WildeQIT_EADamping_channelMutualInfo_additive
-- name    : WildeQIT.EADamping.channelMutualInfo_additive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:25.254364+00:00
-- url     : https://prove2.me/theorems/5f045ee6-c8e7-4078-9088-ec19ec6c996f
-- title:
--   Theorem 13.4.1 (Additivity of the mutual information of quantum channels): $I(\mathcal N\otimes\mathcal M)=I(\mathcal N)+I(\mathcal M)$
-- statement:
--   Let $\mathcal N_{A_1'\to B_1}$ and $\mathcal M_{A_2'\to B_2}$ be any quantum channels on finite-dimensional systems, and let $I(\cdot)$ denote the mutual information of a channel, $I(\mathcal N)=\max_{\varphi_{AA'}}I(A;B)_{\mathcal N(\varphi)}$ over pure inputs. Then the mutual information of the tensor-product channel is the sum of the individual mutual informations:
--
--   $$
--   I(\mathcal N\otimes\mathcal M)=I(\mathcal N)+I(\mathcal M).
--   $$
--
--   The inputs of $\mathcal N\otimes\mathcal M$ range over all pure states $\varphi_{AA_1'A_2'}$, including those entangled across $A_1'A_2'$; additivity says such entanglement does not help, so the channel mutual information needs no regularization.
--
--   **Formalization Note** Finite dimensions, logarithms base 2. $I(\cdot)$ is `channelMutualInfo`, a supremum over pure inputs with a reference of any finite dimension; the tensor-product channel is `tensorChannel`.
--
--   Differences from the source:
--   - encoding: input Hilbert spaces of channels (dimension at least one) → `[Nonempty a] [Nonempty c]`; reason: with an empty input type there is no input state and the book's maximum is undefined, while Lean's supremum would return the junk value 0
--   - encoding: $\max_{\varphi_{AA'}}$ → `⨆` over pure inputs with reference `Fin m`; reason: every finite-dimensional reference is isometric to some $\mathbb C^m$ and the maximum is attained, so the value is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4.1, Theorem 13.4.1, p. 407, (13.122)

import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_Degradable_tensorChannel

namespace WildeQIT.EADamping

open WildeQIT

/-- **Theorem 13.4.1 (Additivity of Quantum Mutual Information of Quantum Channels).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.4.1, (13.122),
p. 407: for any quantum channels `N` and `M`, `I(N ⊗ M) = I(N) + I(M)`.

The inputs of `N ⊗ M` range over all pure states `φ_{AA′₁A′₂}`, entangled across `A′₁A′₂`.

**Formalization Note.** Finite dimensions, bits. `I(·)` is `channelMutualInfo`, the supremum over
pure inputs with a reference of any finite dimension. The input spaces are nonempty (a Hilbert
space of a quantum system has dimension at least one; with an empty input there is no input
state and the book's quantity is undefined). -/
theorem channelMutualInfo_additive {a b c d : Type} [Fintype a] [Fintype b] [Fintype c]
    [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    [Nonempty a] [Nonempty c] (N : QChannel a b) (M : QChannel c d) :
    channelMutualInfo (WildeQIT.Degradable.tensorChannel N M) = channelMutualInfo N + channelMutualInfo M := by sorry

end WildeQIT.EADamping
