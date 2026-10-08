-- Prove2me | Theorems.Thm_StochIneqPO_DBar_theorem7_stationary_coupling
-- name    : StochIneqPO.DBar.theorem7_stationary_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:39.944382+00:00
-- url     : https://prove2.me/theorems/cc049298-de63-4dbc-9dbd-332e8edf35d3
-- title:
--   Theorem 7 — stationary monotone coupling
-- statement:
--   Let $E$ be a partially ordered Polish space with a closed order and Borel measurable structure. Let $P,Q$ be stationary probability laws on $E^{\mathbb Z}$, with its coordinatewise order, and suppose $P\prec Q$. Then there is a stationary probability law $\nu$ on pairs of paths whose marginals are $P,Q$ and which concentrates on ordered pairs:
--
--   $$\nu\{(\omega_1,\omega_2):\omega_1\leq\omega_2\}=1.$$
--
--   This supplies the ordered stationary coupling used in Lemma 3. The paper derives it from its general coupling characterization, Theorem 1(ii).
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 7, p. 909 (PDF p. 11)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant

namespace StochIneqPO.DBar

open MeasureTheory

/-- Theorem 7, p. 909: stationary laws ordered stochastically admit a stationary monotone coupling. -/
theorem theorem7_stationary_coupling
    {E : Type*} [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P Q : Measure (ℤ → E))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPQ : StochIneqPO.Comparison.StochLE P Q) :
    ∃ ν : Measure ((ℤ → E) × (ℤ → E)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
      (∀ᵐ z ∂ν, z.1 ≤ z.2) := by sorry

end StochIneqPO.DBar
