-- Prove2me | Theorems.Thm_ShirokovPM_atomic_barycenter
-- name    : ShirokovPM.atomic_barycenter
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:58.76584+00:00
-- url     : https://prove2.me/theorems/dd1f6648-72d5-411f-b413-8b68fd727391
-- title:
--   §2 — the barycenter of an atomic measure $\{\pi_i,\rho_i\}$ is the average state $\sum_i\pi_i\rho_i$
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $\mathcal A\subseteq\mathfrak S(\mathcal H)$ a closed set of states. Let $\{\rho_i\}_{i\ge0}\subset\mathcal A$ be states and $\{\pi_i\}_{i\ge0}$ a probability vector ($\pi_i\ge0$, $\sum_i\pi_i=1$). Then the atomic measure
--
--   $$
--   \{\pi_i,\rho_i\}=\sum_i\pi_i\,\delta_{\rho_i}
--   $$
--
--   is a Borel probability measure on $\mathcal A$, the series $\sum_i\pi_i\rho_i$ converges in trace norm to a state $\rho$ (the **average state** of the ensemble), and
--
--   $$
--   \mathbf b(\{\pi_i,\rho_i\})=\sum_i\pi_i\rho_i=\rho .
--   $$
--
--   Discrete ensembles of quantum states are thus a special case of barycentric decompositions, with the average state as barycenter.
--
--   **Formalization Note** Countable ensembles are indexed by $\mathbb N$. A finite ensemble is the case in which the weights vanish from some index on, and the Dirac measure $\delta_\rho$ is the case $\pi=(1,0,0,\dots)$. "$\rho$ is the average state" is the published `StateEnsemble b π s ρ` (nonnegative summable weights of total one, partial sums converging to $\rho$ in trace norm), and the barycenter is the published relation `StateBarycenter`.
--
--   Differences from the source:
--   - encoding: separable Hilbert space ℋ → complex Hilbert space with a Hilbert basis indexed by a countable type; reason: a Hilbert space is separable iff it has a countable Hilbert basis, so no instance changes
--   - encoding: atomic measure {πᵢ, ρᵢ} with countably or finitely many atoms → Σᵢ ofReal(πᵢ) δ_{ρᵢ} over i ∈ ℕ, atoms allowed to repeat and weights allowed to vanish; reason: every countable or finite ensemble is of this form, and repeated atoms only merge weights
--   - encoding: b(µ) = Σᵢ πᵢρᵢ → the series converges in trace norm to a state ρ and ρ satisfies the barycenter relation for µ; reason: the barycenter relation characterizes the Bochner integral (matrix elements)
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §2, p.3 ("An atomic measure in 𝒫(𝒜) consisting of the atoms {ρᵢ} ⊂ 𝒜 with the corresponding weights {πᵢ} will be denoted {πᵢ, ρᵢ}. … If µ = {πᵢ, ρᵢ} then b(µ) = Σᵢ πᵢρᵢ is the average state of the ensemble {πᵢ, ρᵢ}")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The barycenter of an atomic measure is the average state of the ensemble.** Shirokov,
arXiv:math-ph/0607019v4, §2, p.3: "An atomic measure in 𝒫(𝒜) consisting of the atoms {ρᵢ} ⊂ 𝒜
with the corresponding weights {πᵢ} will be denoted {πᵢ, ρᵢ}. … If µ = {πᵢ, ρᵢ} then
b(µ) = Σᵢ πᵢρᵢ is the average state of the ensemble {πᵢ, ρᵢ}."

Let `A` be a closed set of states, `(ρᵢ)_{i ∈ ℕ}` states in `A` and `(πᵢ)` a probability vector
(`πᵢ ≥ 0`, `Σ πᵢ = 1`). Then the atomic measure `{πᵢ, ρᵢ} = Σᵢ πᵢ δ_{ρᵢ}` on `A` is a probability
measure, the series `Σᵢ πᵢρᵢ` converges in trace norm to a state `ρ`, and `ρ` is the barycenter of
`{πᵢ, ρᵢ}`.

**Formalization Note** Countable ensembles are indexed by `ℕ`; finite ensembles are the case of
weights vanishing from some index on, and the Dirac measure `δ_ρ` is the case `π = (1, 0, 0, …)`.
"`ρ` is the average state" is the published `StateEnsemble b π s ρ` (nonnegative summable weights
of total one, partial sums converging to `ρ` in trace norm); the barycenter is the published
relation `StateBarycenter`. -/
theorem atomic_barycenter {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} [Countable I] (b : HilbertBasis I ℂ H)
    (A : Set (QuantumState b)) (hA : IsClosed A) (π : ℕ → ℝ) (s : ℕ → A)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ1 : ∑' i, π i = 1) :
    IsProbabilityMeasure (Measure.sum fun i => ENNReal.ofReal (π i) • Measure.dirac (s i)) ∧
      ∃ ρ : QuantumState b, StateEnsemble b π (fun i => (s i).val) ρ ∧
        StateBarycenter b (fun σ : A => σ.val)
          (Measure.sum fun i => ENNReal.ofReal (π i) • Measure.dirac (s i)) ρ := by sorry

end ShirokovPM
