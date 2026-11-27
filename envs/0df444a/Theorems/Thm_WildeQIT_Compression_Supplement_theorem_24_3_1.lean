-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_24_3_1
-- name    : WildeQIT.Compression.Supplement.theorem_24_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:20:36.381771+00:00
-- url     : https://prove2.me/theorems/202f1302-8cc0-51f1-a8b1-0697455537e2
-- title:
--   Theorem 24.3.1 (Quantum Capacity): $C_Q(\mathcal N)=Q_{\mathrm{reg}}(\mathcal N)$
-- statement:
--   The quantum capacity of a quantum channel $\mathcal N_{A'\to B}$ equals its regularized coherent information:
--
--   $$
--   C_Q(\mathcal N)=Q_{\mathrm{reg}}(\mathcal N)=\lim_{k\to\infty}\frac1kQ(\mathcal N^{\otimes k}),\qquad Q(\mathcal N)=\max_{\varphi_{AA'}}I(A\rangle B)_\sigma,\quad\sigma_{AB}=\mathcal N_{A'\to B}(\varphi_{AA'}),
--   $$
--
--   where the maximum is over pure bipartite inputs and $C_Q(\mathcal N)$ is the supremum of achievable rates of quantum communication (§24.2: codes good for every pure input $|\phi\rangle_{RA_1}$).
--
--   The statement includes that the limit exists.
--
--   **Formalization Note** $C_Q$ is the published `WildeQIT.QErasure.quantumCapacity`, $Q$ the published `WildeQIT.Degradable.coherentInfoChannel`, $\mathcal N^{\otimes k}$ the published tensor power. The convergence is stated in the extended reals.
--
--   Differences from the source:
--   - encoding: C_Q(N) = Q_reg(N) with Q_reg(N) ≡ lim_k (1/k) Q(N^{⊗k}) → Tendsto (fun k => Q(N^{⊗k})/k) atTop (nhds (quantumCapacity N)) in EReal; reason: asserts that the limit exists and equals C_Q(N), without a default value for a nonexistent limit
--   - encoding: Hilbert spaces of positive dimension (implicit) → `[Nonempty a]` on the input space; reason: a zero-dimensional space has no state, and the suprema defining the quantities would be empty; the hypothesis excludes only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.3.1, p. 661, eqs. (24.7)–(24.9); §24.2, p. 659

import Mathlib
import Definitions.Def_WildeQIT_QErasure_quantumCapacity
import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.3.1, p. 661.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 24.3.1 (Quantum Capacity)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 661, (24.7)–(24.9)): "The quantum capacity
`C_Q(N)` of a quantum channel `N_{A′→B}` is equal to the regularized coherent information of the
channel: `C_Q(N) = Q_reg(N)`, where `Q_reg(N) ≡ lim_{k→∞} (1/k) Q(N^{⊗k})`. The channel coherent
information `Q(N)` is defined as `Q(N) ≡ max_φ I(A⟩B)_σ`, where the optimization is with respect
to all pure, bipartite states `φ_AA′` and `σ_AB ≡ N_{A′→B}(φ_AA′)`."

Formalization Note: the limit is asserted to exist and to equal `C_Q(N)`, in `EReal`. `C_Q(N)` is
the published `WildeQIT.QErasure.quantumCapacity` (§24.2: codes good for every pure input
`|ϕ⟩_{RA₁}`, (24.2)); `Q` is the published `WildeQIT.Degradable.coherentInfoChannel` (Definition
13.5.1, the book's (24.9)); `N^{⊗k}` is the published `WildeQIT.Degradable.tensorPower`. The input
space is nonempty. -/
theorem theorem_24_3_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    Filter.Tendsto
      (fun k : ℕ => ((WildeQIT.Degradable.coherentInfoChannel
        (WildeQIT.Degradable.tensorPower N k) / k : ℝ) : EReal))
      Filter.atTop (nhds (WildeQIT.QErasure.quantumCapacity N)) := by sorry

end WildeQIT.Compression.Supplement
