-- Prove2me | Theorems.Thm_ShirokovPM_barycenter_map_continuous_surjective
-- name    : ShirokovPM.barycenter_map_continuous_surjective
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:51.736143+00:00
-- url     : https://prove2.me/theorems/62135767-97d9-4060-b316-067ccaaee0a1
-- title:
--   §4, (1) — the barycenter map $\mathcal P(\mathfrak S(\mathcal H))\ni\mu\mapsto\mathbf b(\mu)\in\mathfrak S(\mathcal H)$ is a continuous surjection
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space. The barycenter map
--
--   $$
--   \mathcal P(\mathfrak S(\mathcal H))\ni\mu\mapsto\mathbf b(\mu)=\int_{\mathfrak S(\mathcal H)}\sigma\,\mu(d\sigma)\in\mathfrak S(\mathcal H)
--   $$
--
--   is continuous, from the topology of weak convergence of measures to the trace-norm topology on states, and surjective.
--
--   Precisely: there is a map $\beta:\mathcal P(\mathfrak S(\mathcal H))\to\mathfrak S(\mathcal H)$ such that $\beta(\mu)$ is the barycenter of $\mu$ for every $\mu$, $\beta$ is continuous, and every state is $\beta(\mu)$ for some $\mu$.
--
--   Continuity of the barycenter map is what makes the preimage $\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))=\mathbf b^{-1}(\mathcal A)$ of a closed set closed, and what transports compactness from measures back to states.
--
--   **Formalization Note** $\mathcal P(\mathfrak S(\mathcal H))$ is Mathlib's `ProbabilityMeasure (QuantumState b)` with the weak topology. Since the published relation `StateBarycenter` determines its state uniquely (matrix elements), $\beta$ is the paper's map $\mathbf b$.
--
--   Differences from the source:
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
--   - encoding: the map µ ↦ b(µ) → existence of a map β with StateBarycenter b id µ (β µ) for all µ; reason: the barycenter relation determines its state uniquely, so β is the barycenter map
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §4, display (1), p.5 ("The barycenter map 𝒫(𝔖(ℋ)) ∋ µ ↦ b(µ) ∈ 𝔖(ℋ) (1) is a continuous surjection [13]")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The barycenter map is a continuous surjection.** Shirokov, arXiv:math-ph/0607019v4, §4,
display (1), p.5: "The barycenter map 𝒫(𝔖(ℋ)) ∋ µ ↦ b(µ) ∈ 𝔖(ℋ) (1) is a continuous
surjection [13]."

There is a map `β : 𝒫(𝔖(ℋ)) → 𝔖(ℋ)` such that `β(μ)` is the barycenter of `μ` for every `μ`, `β`
is continuous from the weak topology to the trace-norm topology, and `β` is onto.

**Formalization Note** `ℋ` has a countable Hilbert basis `b` (a separable Hilbert space);
`𝒫(𝔖(ℋ))` is Mathlib's `ProbabilityMeasure (QuantumState b)` with the topology of weak
convergence and `𝔖(ℋ)` carries the trace-norm topology. The barycenter is the published relation
`StateBarycenter`, which determines a state uniquely (its matrix elements), so `β` is the paper's
map `b`. -/
theorem barycenter_map_continuous_surjective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) :
    ∃ β : ProbabilityMeasure (QuantumState b) → QuantumState b,
      (∀ μ : ProbabilityMeasure (QuantumState b), StateBarycenter b id (μ : Measure (QuantumState b)) (β μ)) ∧
        Continuous β ∧ Function.Surjective β := by sorry

end ShirokovPM
