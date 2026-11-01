-- Prove2me | Theorems.Thm_WildeQIT_Degradable_corollary_13_5_1
-- name    : WildeQIT.Degradable.corollary_13_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:49.961749+00:00
-- url     : https://prove2.me/theorems/29140e67-d635-4fd3-bd8e-3e50dfdba07d
-- title:
--   Corollary 13.5.1 — regularized coherent information of a degradable channel equals its coherent information
-- statement:
--   **Corollary 13.5.1.** The regularized coherent information of a degradable quantum channel $\mathcal N$ is equal to its coherent information:
--
--   $$
--   Q_{\mathrm{reg}}(\mathcal N)=Q(\mathcal N),\qquad Q_{\mathrm{reg}}(\mathcal N)\equiv\lim_{n\to\infty}\frac1n Q(\mathcal N^{\otimes n}).
--   $$
--
--   That is, the limit exists and equals the single-letter value; for degradable channels this gives a single-letter formula for the quantum capacity.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: Q(·) defined as a maximum over inputs → Q(·) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: degradable: D ∘ N = N^c for a channel N^c complementary to N → IsDegradable: a Kraus channel D from B to the environment of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ with D(N(ρ)) = N^c(ρ) for every density operator ρ; reason: two complementary channels differ by an isometry (or partial isometry) on the environment, so degradability does not depend on the choice
--   - encoding: Q_reg(N) = Q(N) with Q_reg(N) ≡ lim_n (1/n) Q(N^⊗n) → Tendsto (fun n => Q(N^⊗n) / n) atTop (𝓝 Q(N)); reason: the book's equation asserts that the limit exists and equals the single-letter value; the n = 0 term (division by 0) does not affect the limit
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 13.5.1, p. 414 (regularization as in (13.9), p. 389, and (13.182), p. 416)

import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 13.5.1, p. 414.
-/

open Filter Topology

namespace WildeQIT.Degradable

/-- **Corollary 13.5.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 414). The regularized coherent information of a degradable
quantum channel is equal to its coherent information: `Q_reg(N) = Q(N)`, where
`Q_reg(N) ≡ lim_{n→∞} (1/n) Q(N^{⊗n})` (the analogue of (13.9) and (13.182)).

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. "`Q_reg(N) = Q(N)`" is stated as: the sequence `Q(N^{⊗n})/n` converges
to `Q(N)`, which asserts that the limit defining `Q_reg` exists and equals `Q(N)`. Degradability
is Definition 13.5.2 (`IsDegradable`). -/
theorem corollary_13_5_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) (hN : IsDegradable N) :
    Tendsto (fun n : ℕ => coherentInfoChannel (tensorPower N n) / n) atTop
      (𝓝 (coherentInfoChannel N)) := by sorry

end WildeQIT.Degradable
