-- Prove2me | Theorems.Thm_ShirokovPM_tight_of_barycenter_mem_compact
-- name    : ShirokovPM.tight_of_barycenter_mem_compact
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:33.194988+00:00
-- url     : https://prove2.me/theorems/deda162c-3a51-4a22-9f1f-1886948b3499
-- title:
--   §3 — Prokhorov step: $\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))$ is tight for compact $\mathcal A$
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $\mathcal A\subseteq\mathfrak S(\mathcal H)$ a set of states that is compact in the trace-norm topology. Then the family
--
--   $$
--   \mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))=\{\mu\in\mathcal P(\mathfrak S(\mathcal H)) : \mathbf b(\mu)\in\mathcal A\}
--   $$
--
--   is **tight**: for every $\varepsilon>0$ there is a trace-norm compact set $\mathcal K\subseteq\mathfrak S(\mathcal H)$ with
--
--   $$
--   \mu\bigl(\mathfrak S(\mathcal H)\setminus\mathcal K\bigr)\le\varepsilon\qquad\text{for all }\mu\in\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H)).
--   $$
--
--   This is the claim to which the paper applies Prokhorov's theorem to obtain the "if" direction of Theorem 1 when $\dim\mathcal H=+\infty$.
--
--   **Formalization Note** Tightness is Mathlib's `IsTightMeasureSet` for the trace-norm topology, applied to the image of $\mathcal P_{\mathcal A}(\mathfrak S(\mathcal H))$ in the space of measures.
--
--   Differences from the source:
--   - generalization: the case dim ℋ = +∞ → every separable ℋ (countable Hilbert basis), finite-dimensional and zero included; reason: the source invokes Prokhorov only when dim ℋ = +∞ because 𝒫(𝔖(ℋ)) is already compact otherwise; the Lean statement specializes to the source's case
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §3, p.3 ("But in the case dim ℋ = +∞ the following compactness criterion for subsets of 𝒫(𝔖(ℋ)) can be proved by using Prokhorov's theorem [13, Proposition 2]"); the tightness claim is the hypothesis of Prokhorov's theorem in the proof of Theorem 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34
import Definitions.Def_ShirokovPM_measuresWithBarycenterIn

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The Prokhorov step: measures with barycenter in a compact set form a tight family.**
Shirokov, arXiv:math-ph/0607019v4, §3, p.3: "But in the case dim ℋ = +∞ the following
compactness criterion for subsets of 𝒫(𝔖(ℋ)) can be proved by using Prokhorov's theorem
[13, Proposition 2]."

For every trace-norm compact set `A ⊆ 𝔖(ℋ)`, the family `𝒫_A(𝔖(ℋ))` of Borel probability
measures on `𝔖(ℋ)` with barycenter in `A` is tight: for every `ε > 0` there is a compact
`K ⊆ 𝔖(ℋ)` with `μ(𝔖(ℋ) ∖ K) ≤ ε` for all `μ ∈ 𝒫_A(𝔖(ℋ))`.

**Formalization Note** Stated for every separable `ℋ` (countable Hilbert basis `b`), not only
`dim ℋ = +∞`; tightness is Mathlib's `IsTightMeasureSet` for the trace-norm topology. -/
theorem tight_of_barycenter_mem_compact {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) (hA : IsCompact A) :
    IsTightMeasureSet
      ((fun μ : ProbabilityMeasure (QuantumState b) => (μ : Measure (QuantumState b))) ''
        measuresWithBarycenterIn b A) := by sorry

end ShirokovPM
