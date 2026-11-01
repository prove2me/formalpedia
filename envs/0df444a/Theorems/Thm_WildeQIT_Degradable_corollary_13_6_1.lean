-- Prove2me | Theorems.Thm_WildeQIT_Degradable_corollary_13_6_1
-- name    : WildeQIT.Degradable.corollary_13_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:59:08.638526+00:00
-- url     : https://prove2.me/theorems/7aa3dd65-476a-4ea3-b46a-5459ba2c007c
-- title:
--   Corollary 13.6.1 — regularized private information of a degradable channel equals its private information
-- statement:
--   **Corollary 13.6.1.** Suppose that a quantum channel $\mathcal N$ is degradable. Then the regularized private information $P_{\mathrm{reg}}(\mathcal N)$ of the channel is equal to its private information $P(\mathcal N)$:
--
--   $$
--   P_{\mathrm{reg}}(\mathcal N)=P(\mathcal N),\qquad P_{\mathrm{reg}}(\mathcal N)=\lim_{n\to\infty}\frac1nP(\mathcal N^{\otimes n}).
--   $$
--
--   That is, the limit (13.182) exists and equals the single-letter value; for degradable channels this gives a single-letter formula for the private classical capacity.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: P(·) defined as a maximum over inputs → P(·) defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: degradable: D ∘ N = N^c for a channel N^c complementary to N → IsDegradable: a Kraus channel D from B to the environment of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ with D(N(ρ)) = N^c(ρ) for every density operator ρ; reason: two complementary channels differ by an isometry (or partial isometry) on the environment, so degradability does not depend on the choice
--   - encoding: P_reg(N) = P(N) with P_reg(N) ≡ lim_n (1/n) P(N^⊗n) → Tendsto (fun n => P(N^⊗n) / n) atTop (𝓝 P(N)); reason: the book's equation asserts that the limit exists and equals the single-letter value; the n = 0 term (division by 0) does not affect the limit
--   - encoding: I(X;B) and I(X;E) evaluated on U^N(ρ_XA′) for an isometric extension U^N of N → the classical–quantum states Σ_x p(x)|x⟩⟨x| ⊗ N(ρ^x) and Σ_x p(x)|x⟩⟨x| ⊗ N^c(ρ^x), with N^c the complementary channel of the canonical isometric extension U = Σ_i K_i ⊗ |i⟩ (environment N.ι); reason: the XB and XE marginals of U^N(ρ_XA′) are these states, and any two isometric extensions differ by an isometry on the environment, which leaves I(X;E) unchanged
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 13.6.1, eq. (13.225), p. 421 (regularization (13.182), p. 416)

import Definitions.Def_WildeQIT_Degradable_privateInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 13.6.1, p. 421.
-/

open Filter Topology

namespace WildeQIT.Degradable

/-- **Corollary 13.6.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 421, eq. (13.225)). Suppose that a quantum channel `N` is
degradable. Then the regularized private information `P_reg(N)` of the channel is equal to its
private information `P(N)`: `P_reg(N) = P(N)`, where `P_reg(N) = lim_{n→∞} (1/n) P(N^{⊗n})`
(13.182), p. 416.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. "`P_reg(N) = P(N)`" is stated as: the sequence `P(N^{⊗n})/n` converges
to `P(N)`, which asserts that the limit (13.182) exists and equals `P(N)`. -/
theorem corollary_13_6_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) (hN : IsDegradable N) :
    Tendsto (fun n : ℕ => privateInfoChannel (tensorPower N n) / n) atTop
      (𝓝 (privateInfoChannel N)) := by sorry

end WildeQIT.Degradable
