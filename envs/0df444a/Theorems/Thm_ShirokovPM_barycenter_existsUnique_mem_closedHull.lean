-- Prove2me | Theorems.Thm_ShirokovPM_barycenter_existsUnique_mem_closedHull
-- name    : ShirokovPM.barycenter_existsUnique_mem_closedHull
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:50.869973+00:00
-- url     : https://prove2.me/theorems/f805aa71-684c-4284-b92c-8a1b717079c4
-- title:
--   §2 — the barycenter $\mathbf b(\mu)$ is a well-defined state in $\overline{\mathrm{co}}(\mathcal A)$
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $\mathcal A\subseteq\mathfrak S(\mathcal H)$ a closed set of states, with the trace-norm topology. For every Borel probability measure $\mu\in\mathcal P(\mathcal A)$ the Bochner integral
--
--   $$
--   \mathbf b(\mu)=\int_{\mathcal A}\sigma\,\mu(d\sigma)
--   $$
--
--   exists and is a state in the trace-norm closed convex hull $\overline{\mathrm{co}}(\mathcal A)$. Precisely: there is a state $\rho\in\overline{\mathrm{co}}(\mathcal A)$ such that every matrix element $\sigma\mapsto\langle x,\sigma y\rangle$ is $\mu$-integrable and
--
--   $$
--   \langle x,\rho\,y\rangle=\int_{\mathcal A}\langle x,\sigma y\rangle\,\mu(d\sigma)\qquad(x,y\in\mathcal H),
--   $$
--
--   and $\rho$ is the only state with this property.
--
--   This makes the barycenter map $\mu\mapsto\mathbf b(\mu)$ well defined on every $\mathcal P(\mathcal A)$; in particular no measure is lost from the sets $\mathcal P_{\mathcal B}(\mathcal A)$ for lack of a barycenter.
--
--   **Formalization Note** $\mathfrak S(\mathcal H)$ is the published `QuantumState b`, $\mathcal A$ carries the subspace topology and its Borel $\sigma$-algebra, $\overline{\mathrm{co}}(\mathcal A)$ is the published `stateClosedHull b A`, and the barycenter is the published relation `StateBarycenter`.
--
--   Differences from the source:
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
--   - encoding: b(µ) defined as the trace-norm Bochner integral → existence and uniqueness of a state ρ in co̅(𝒜) whose matrix elements are the integrals of the matrix elements (with their integrability); reason: matrix elements determine an operator, and the Bochner integral commutes with the continuous functionals T ↦ ⟨x, T y⟩, so the relation holds exactly for the Bochner integral
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §2, p.3 ("The barycenter of a measure µ ∈ 𝒫(𝒜) is the state in co̅(𝒜) defined by the Bochner integral b(µ) = ∫_𝒜 σµ(dσ)", for closed 𝒜 as in the preceding paragraph)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The barycenter is a well-defined state in the closed convex hull.** Shirokov,
arXiv:math-ph/0607019v4, §2, p.3: "The barycenter of a measure µ ∈ 𝒫(𝒜) is the state in co̅(𝒜)
defined by the Bochner integral b(µ) = ∫_𝒜 σµ(dσ)."

For every closed set `A` of states and every Borel probability measure `μ` on `A` there is a
state `ρ` in the trace-norm closed convex hull `co̅(A)` that is the barycenter of `μ`, and it is
the only state that is the barycenter of `μ`.

**Formalization Note** `ℋ` is a complex Hilbert space with a countable Hilbert basis `b`
(equivalently, a separable Hilbert space, including the finite-dimensional and zero cases);
`𝔖(ℋ)` is the published `QuantumState b` with the trace-norm topology, `A` carries the subspace
topology and its Borel σ-algebra; `co̅(A)` is the published `stateClosedHull b A`. The barycenter
is the published relation `StateBarycenter`: every matrix element `⟨x, σ y⟩` is `μ`-integrable and
`⟨x, ρ y⟩ = ∫ ⟨x, σ y⟩ μ(dσ)`; existence therefore includes integrability. -/
theorem barycenter_existsUnique_mem_closedHull {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) (hA : IsClosed A)
    (μ : ProbabilityMeasure A) :
    ∃ ρ ∈ stateClosedHull b A,
      StateBarycenter b (fun σ : A => σ.val) (μ : Measure A) ρ ∧
      ∀ ρ' : QuantumState b,
        StateBarycenter b (fun σ : A => σ.val) (μ : Measure A) ρ' → ρ' = ρ := by sorry

end ShirokovPM
