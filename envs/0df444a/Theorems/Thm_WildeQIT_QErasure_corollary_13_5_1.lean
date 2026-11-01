-- Prove2me | Theorems.Thm_WildeQIT_QErasure_corollary_13_5_1
-- name    : WildeQIT.QErasure.corollary_13_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:58.606218+00:00
-- url     : https://prove2.me/theorems/4c69f28e-2673-47ea-a880-28a0390bc860
-- title:
--   Corollary 13.5.1: $Q_{\mathrm{reg}}(\mathcal N)=Q(\mathcal N)$ for degradable channels
-- statement:
--   Let $\mathcal N$ be a degradable quantum channel. Then its regularized coherent information equals its coherent information:
--
--   $$
--   Q_{\mathrm{reg}}(\mathcal N)\equiv\lim_{n\to\infty}\frac1n\,Q(\mathcal N^{\otimes n})=Q(\mathcal N).
--   $$
--
--   Combined with the quantum capacity theorem $C_Q=Q_{\mathrm{reg}}$, this makes the quantum capacity of a degradable channel single-letter.
--
--   **Formalization Note** "$Q_{\mathrm{reg}}(\mathcal N)=Q(\mathcal N)$" is stated as convergence of $Q(\mathcal N^{\otimes n})/n$ to $Q(\mathcal N)$, which asserts that the limit exists and equals $Q(\mathcal N)$.
--
--   Differences from the source:
--   - encoding: Q_reg(N) = Q(N), with Q_reg(N) ≡ lim (1/k) Q(N^⊗k) → Tendsto (fun n => coherentInfoChannel (tensorPower N n) / n) atTop (𝓝 (coherentInfoChannel N)); reason: states that the limit exists and has the value Q(N)
--   - encoding: an input Hilbert space → a nonempty finite index type a; reason: a Hilbert space carrying a state has dimension at least one
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 13.5.1, p. 414; Q_reg as in (24.8), p. 661

import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 13.5.1, p. 414.
-/

open Filter Topology

namespace WildeQIT.QErasure

/-- **Corollary 13.5.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 414). The regularized coherent information of a degradable
quantum channel is equal to its coherent information: `Q_reg(N) = Q(N)`, where
`Q_reg(N) ≡ lim_{n→∞} (1/n) Q(N^{⊗n})` ((24.8), p. 661; the analogue of (13.9)).

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. "`Q_reg(N) = Q(N)`" is stated as: the sequence `Q(N^{⊗n})/n` converges
to `Q(N)`, which asserts that the limit defining `Q_reg` exists and equals `Q(N)`. Degradability
is Definition 13.5.2 (`IsDegradable`). -/
theorem corollary_13_5_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) (hN : WildeQIT.Degradable.IsDegradable N) :
    Tendsto (fun n : ℕ => WildeQIT.Degradable.coherentInfoChannel (WildeQIT.Degradable.tensorPower N n) / n) atTop
      (𝓝 (WildeQIT.Degradable.coherentInfoChannel N)) := by sorry

end WildeQIT.QErasure
