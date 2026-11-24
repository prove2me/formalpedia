-- Prove2me | Theorems.Thm_WilliamsonShmoys_RAMSpec_loop
-- name    : WilliamsonShmoys.RAMSpec.loop
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:58.287037+00:00
-- url     : https://prove2.me/theorems/7036fac4-758f-44b1-86fd-5808260a018f
-- title:
--   Loop rule with a decreasing measure
-- statement:
--   Let $I$ be an invariant, $E$ an exit condition and $\mu$ a natural-number measure on states. Suppose that from every state satisfying $I$ but not $E$, running $p$ reaches, within $c$ operations, a state satisfying $I$ with strictly smaller $\mu$. Then for every $m$,
--
--   $$\{I\wedge \mu\le m\}\;p\;\{I\wedge E\}_{\le c\,m}.$$
--
--   This is the total-correctness rule for loops; the cost is the per-iteration bound times the number of iterations, bounded by the initial measure.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.RAMSpec.loop (program : List PlanarRAMInstruction)
    (I E : PlanarRAMState → Prop) (μ : PlanarRAMState → ℕ) (c : ℕ)
    (hbody : ∀ s, I s → ¬ E s →
      RAMReachesWithin program s (fun s' => I s' ∧ μ s' < μ s) c)
    (m : ℕ) :
    RAMSpec program (fun s => I s ∧ μ s ≤ m) (fun s => I s ∧ E s) (c * m) := by sorry
