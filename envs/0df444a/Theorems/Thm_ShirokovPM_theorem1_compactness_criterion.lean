-- Prove2me | Theorems.Thm_ShirokovPM_theorem1_compactness_criterion
-- name    : ShirokovPM.theorem1_compactness_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:54.368242+00:00
-- url     : https://prove2.me/theorems/c8432a73-b2fd-4858-bde6-c046d27ee0dc
-- title:
--   Theorem 1 — $\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))$ is compact if and only if $\mathcal A$ is compact
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space, $\mathfrak S(\mathcal H)$ the set of density operators on $\mathcal H$ with the trace-norm topology, and $\mathcal P(\mathfrak S(\mathcal H))$ the set of Borel probability measures on $\mathfrak S(\mathcal H)$ with the topology of weak convergence. For an arbitrary set $\mathcal A\subseteq\mathfrak S(\mathcal H)$ (not necessarily closed), let
--
--   $$
--   \mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))=\Bigl\{\mu\in\mathcal P(\mathfrak S(\mathcal H)) : \mathbf b(\mu)=\int_{\mathfrak S(\mathcal H)}\sigma\,\mu(d\sigma)\in\mathcal A\Bigr\}
--   $$
--
--   be the set of measures whose barycenter lies in $\mathcal A$. Then
--
--   $$
--   \mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))\ \text{is compact}\quad\Longleftrightarrow\quad\mathcal A\ \text{is compact}.
--   $$
--
--   When $\dim\mathcal H=+\infty$ the whole space $\mathcal P(\mathfrak S(\mathcal H))$ is not compact, yet each preimage of a compact set of states under the barycenter map is. This is the property later called $\mu$-compactness of $\mathfrak S(\mathcal H)$. It yields the Choquet-type decomposition and the semicontinuity results of the paper's §3 (Corollaries 1–4).
--
--   **Formalization Note** $\mathcal H$ has a countable Hilbert basis $b$, $\mathfrak S(\mathcal H)$ is the published `QuantumState b`, $\mathcal P(\mathfrak S(\mathcal H))$ is Mathlib's `ProbabilityMeasure` with the weak topology, and $\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))$ is `measuresWithBarycenterIn b A`, defined through the published barycenter relation `StateBarycenter`. The case $\mathcal H=0$ (no states) and the finite-dimensional case are instances, not exclusions.
--
--   Differences from the source:
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
--   - encoding: 𝒫_𝒜(𝔖(ℋ)) = {µ : b(µ) ∈ 𝒜} → {µ : ∃ ρ ∈ 𝒜, StateBarycenter b id µ ρ}; reason: every µ has exactly one state satisfying the barycenter relation, namely the Bochner integral b(µ) (milestone barycenter_existsUnique_mem_closedHull with 𝒜 = 𝔖(ℋ)), so the two sets coincide
--   - reading: Theorem 1 is introduced by "But in the case dim ℋ = +∞ the following compactness criterion … can be proved", while its own sentence has no dimension hypothesis → every separable ℋ, finite-dimensional and zero included; reason: the stronger of the two readings, and the one the theorem's sentence states; in finite dimension 𝒫(𝔖(ℋ)) is compact and the barycenter map is a continuous surjection with continuous section ρ ↦ δ_ρ, so the equivalence holds there too
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §3, Theorem 1, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34
import Definitions.Def_ShirokovPM_measuresWithBarycenterIn

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **Theorem 1 (compactness criterion).** Shirokov, arXiv:math-ph/0607019v4, §3, Theorem 1,
p.3: "The set 𝒫_𝒜(𝔖(ℋ)) ⊂ 𝒫(𝔖(ℋ)) is compact if and only if the set 𝒜 ⊂ 𝔖(ℋ) is compact."

For every separable Hilbert space `ℋ` and every set `A ⊆ 𝔖(ℋ)` of states (not necessarily
closed), the set of Borel probability measures on `𝔖(ℋ)` whose barycenter lies in `A` is compact
in the topology of weak convergence if and only if `A` is compact in the trace-norm topology.

**Formalization Note** `ℋ` is a complex Hilbert space with a countable Hilbert basis `b`
(a separable Hilbert space, finite- or infinite-dimensional, possibly zero); `𝔖(ℋ)` is the
published `QuantumState b` with the trace-norm topology and Borel σ-algebra; `𝒫(𝔖(ℋ))` is
Mathlib's `ProbabilityMeasure` with the weak topology; `𝒫_A(𝔖(ℋ))` is
`measuresWithBarycenterIn b A`, defined through the published barycenter relation
`StateBarycenter`. -/
theorem theorem1_compactness_criterion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) :
    IsCompact (measuresWithBarycenterIn b A) ↔ IsCompact A := by sorry

end ShirokovPM
