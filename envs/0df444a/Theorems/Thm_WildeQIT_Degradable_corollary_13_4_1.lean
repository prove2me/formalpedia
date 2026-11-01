-- Prove2me | Theorems.Thm_WildeQIT_Degradable_corollary_13_4_1
-- name    : WildeQIT.Degradable.corollary_13_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:07.217015+00:00
-- url     : https://prove2.me/theorems/d3a54056-a8af-4d14-8270-8f2e126edf6f
-- title:
--   Corollary 13.4.1 — the regularized mutual information of a quantum channel equals its mutual information
-- statement:
--   **Corollary 13.4.1.** The regularized mutual information of a quantum channel $\mathcal N$ is equal to its mutual information:
--
--   $$
--   I_{\mathrm{reg}}(\mathcal N)=I(\mathcal N),\qquad I_{\mathrm{reg}}(\mathcal N)\equiv\lim_{n\to\infty}\frac1n I(\mathcal N^{\otimes n}).
--   $$
--
--   That is, the limit exists and equals the single-letter value $I(\mathcal N)$.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: I(·) defined as a maximum over inputs → I(·) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: I_reg(N) = I(N) with I_reg(N) ≡ lim_n (1/n) I(N^⊗n) → Tendsto (fun n => I(N^⊗n) / n) atTop (𝓝 I(N)); reason: the book's equation asserts that the limit exists and equals the single-letter value; the n = 0 term (division by 0) does not affect the limit
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 13.4.1, eq. (13.132), p. 409 (regularization as in (13.9), p. 389)

import Definitions.Def_WildeQIT_Degradable_mutualInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 13.4.1, p. 409.
-/

open Filter Topology

namespace WildeQIT.Degradable

/-- **Corollary 13.4.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 409, eq. (13.132)). The regularized mutual information of a
quantum channel `N` is equal to its mutual information: `I_reg(N) = I(N)`, where
`I_reg(N) ≡ lim_{n→∞} (1/n) I(N^{⊗n})` (the quantum analogue of (13.9), p. 389).

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. "`I_reg(N) = I(N)`" is stated as: the sequence `I(N^{⊗n})/n`
converges to `I(N)`. This asserts that the limit defining `I_reg` exists and equals `I(N)`. -/
theorem corollary_13_4_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    Tendsto (fun n : ℕ => mutualInfoChannel (tensorPower N n) / n) atTop
      (𝓝 (mutualInfoChannel N)) := by sorry

end WildeQIT.Degradable
