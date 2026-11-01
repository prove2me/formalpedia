-- Prove2me | Theorems.Thm_ShirokovPM_states_closed_convex_polish
-- name    : ShirokovPM.states_closed_convex_polish
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:46.364319+00:00
-- url     : https://prove2.me/theorems/bb956b17-74e5-4228-8c36-6dcf25d9a831
-- title:
--   §2 — $\mathfrak S(\mathcal H)$ is closed and convex in $\mathfrak T(\mathcal H)$ and a complete separable metric space in trace norm
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space, $\mathfrak T(\mathcal H)$ the space of trace-class operators with the trace norm $\|\cdot\|_1$, and $\mathfrak S(\mathcal H)\subset\mathfrak T(\mathcal H)$ the set of positive operators of unit trace (density operators). Then:
--
--   1. $\mathfrak S(\mathcal H)$ is closed in $\mathfrak T(\mathcal H)$ for the trace norm;
--   2. $\mathfrak S(\mathcal H)$ is convex;
--   3. the trace-norm distance
--   $$
--   d(\rho,\sigma)=\|\rho-\sigma\|_1
--   $$
--   is a metric on $\mathfrak S(\mathcal H)$ that induces its topology, and $\mathfrak S(\mathcal H)$ is complete for it;
--   4. $\mathfrak S(\mathcal H)$ is separable.
--
--   So $\mathfrak S(\mathcal H)$ is a Polish space, which is the setting in which the paper applies Prokhorov's theorem to $\mathcal P(\mathfrak S(\mathcal H))$.
--
--   **Formalization Note** $\mathcal H$ has a countable Hilbert basis $b$. $\mathfrak T(\mathcal H)$ is the published `TraceClass H` (nuclear operators) with the published `traceNormTopology`, the trace norm is the published `traceNormValue` (nuclear norm), and the trace is the basis trace. Clause 3 asserts a `MetricSpace` structure on `QuantumState b` whose distance is the trace norm of the difference, whose topology is the installed state topology, and which is complete.
--
--   Differences from the source:
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
--   - encoding: trace norm and trace of 𝔗(ℋ) → nuclear norm (infimum over nuclear representations) and basis trace Σᵢ⟨bᵢ, T bᵢ⟩; reason: equal on trace-class operators
--   - encoding: "complete separable metric space with the metric defined by the trace norm" → existence of a metric structure with dist ρ σ = ‖ρ − σ‖₁ inducing the installed topology and complete, plus separability of the installed topology; reason: Lean's topology on states is installed as an instance, so the metric is asserted to match it
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §2, p.2 ("𝔖(ℋ) – the closed convex subset of 𝔗(ℋ) … which is complete separable metric space with the metric defined by the trace norm")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormTopology traceNormValue IsPositive operatorTrace)
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The state space is a closed convex set and a complete separable metric space.** Shirokov,
arXiv:math-ph/0607019v4, §2, p.2: "𝔖(ℋ) – the closed convex subset of 𝔗(ℋ) consisting of all
positive operators with the unit trace – density operators in ℋ, which is complete separable
metric space with the metric defined by the trace norm."

For a separable Hilbert space `ℋ`:
1. the set of positive trace-class operators of trace one is closed in the trace class `𝔗(ℋ)`
   with the trace-norm topology;
2. it is convex;
3. the trace-norm distance `d(ρ, σ) = ‖ρ − σ‖₁` is a metric on `𝔖(ℋ)` that induces its topology
   and is complete;
4. `𝔖(ℋ)` is separable.

**Formalization Note** `ℋ` has a countable Hilbert basis `b`; `𝔗(ℋ)` is the published
`TraceClass H` (nuclear operators) with the published `traceNormTopology`, the trace norm is the
published `traceNormValue` (nuclear norm) and the trace is the basis trace `operatorTrace b`.
Clause 3 asks for a `MetricSpace` structure whose distance is the trace norm of the difference,
whose topology is the installed state topology and which is complete. -/
theorem states_closed_convex_polish {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) :
    @IsClosed (TraceClass H) traceNormTopology
        {T : TraceClass H | IsPositive T.val ∧ operatorTrace b T.val = 1} ∧
      StateConvex b Set.univ ∧
      (∃ m : MetricSpace (QuantumState b),
        (∀ ρ σ : QuantumState b,
            m.toDist.dist ρ σ = traceNormValue (stateOp b ρ - stateOp b σ)) ∧
          m.toUniformSpace.toTopologicalSpace = quantumStateTopology b ∧
          @CompleteSpace (QuantumState b) m.toUniformSpace) ∧
      TopologicalSpace.SeparableSpace (QuantumState b) := by sorry

end ShirokovPM
