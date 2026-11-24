-- Prove2me | Theorems.Thm_WilliamsonShmoys_RAMSpec_consequence
-- name    : WilliamsonShmoys.RAMSpec.consequence
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:59.413015+00:00
-- url     : https://prove2.me/theorems/436b371d-2fe3-4df9-9d45-a831e28eef5a
-- title:
--   Consequence rule for timed triples
-- statement:
--   If $\{P\}\,p\,\{Q\}_{\le t}$, $P'\Rightarrow P$, $Q\Rightarrow Q'$ and $t\le t'$, then $\{P'\}\,p\,\{Q'\}_{\le t'}$.
--
--   It allows strengthening preconditions, weakening postconditions and relaxing time bounds.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.RAMSpec.consequence (program : List PlanarRAMInstruction)
    (P P' Q Q' : PlanarRAMState → Prop) (t t' : ℕ)
    (h : RAMSpec program P Q t) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s) (ht : t ≤ t') :
    RAMSpec program P' Q' t' := by sorry
