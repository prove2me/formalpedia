-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_explicit_success_bound
-- name    : SFLOracleLowerBound.Hardness.explicit_success_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:27:25.493861+00:00
-- url     : https://prove2.me/theorems/78d3b96b-1d5b-48d0-a5bb-0aa75df9146b
-- title:
--   Proposition 26 — Explicit success-probability bound
-- statement:
--   There are an absolute constant $\alpha_0>0$, a polynomial $P$, and an infinite set of client counts $N$, all chosen before the algorithm, with the following property. For every randomized algorithm using at most $Q$ value queries on every run, there is an SFL instance with $N$ clients, at most $N$ facilities, rational public distances of total encoding length at most $P(N)$, and a matroid-rank facility cost, whose probability of returning an $\alpha_0\log\log N$ approximation is at most
--   $$(Q+N)\exp\left[-\frac19\left(\frac{\log N}{\log\log N}\right)^2\right].$$
--   The hard sizes are independent of the algorithm. This explicit success bound is the quantitative milestone for Theorem 2; its exponent $1/9$ is unchanged.
--
--   Differences from the source:
--   - encoding: arbitrary adaptive randomized exact-value algorithms → transcript strategies with real answers and private seeds on arbitrary probability spaces, with measurable observable runs; reason: all oracle dependence occurs through the transcript; measurability makes the stated probabilities well-defined and no support restriction is imposed
--   - encoding: infinitely many integers N and polynomial rational encoding length → an infinite set of natural sizes N≥16 and a natural-coefficient polynomial bounding the full rational pseudometric matrix; reason: discarding finitely many sizes retains infinitude, makes both logarithms positive, and a natural-coefficient polynomial dominates any polynomial encoding bound
--   - generalization: at most Q queries on every run of every instance → the Q bound is required only on valid matroid-rank SFL inputs with exactly N clients and at most N facilities; reason: the source proof only runs the algorithm on the constructed matroid-rank hidden and reference instances at this fixed size, so the weaker local budget hypothesis covers all source algorithms
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Proposition 26, pp.25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Oracle

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Proposition 26, pp.25–26. Absolute α₀ and polynomial, infinitely many common sizes. -/

theorem explicit_success_bound : ∃ α₀ : ℝ, 0 < α₀ ∧ ∃ P : Polynomial ℕ,
    ∃ sizes : Set ℕ, sizes.Infinite ∧ (∀ N ∈ sizes, 16 ≤ N) ∧
    ∀ N ∈ sizes, ∀ (A : AlgorithmFamily) (Q : ℕ), SizeQueryBound A N Q →
      ∃ (m : ℕ) (D : PublicData (Fin N) (Fin m)) (g : Finset (Fin N) → ℝ),
        0 < m ∧ m ≤ N ∧ IsSFL D ∧ RationalEncoding D P ∧ FacilityCost g ∧ MatroidRank g ∧
        successProbability (A N m D) D g Q (α₀ * Real.log (Real.log N)) ≤
          ((Q : ℝ)+N) * Real.exp (-(1/9 : ℝ) * (Real.log N / Real.log (Real.log N))^2) := by sorry

end SFLOracleLowerBound.Hardness
