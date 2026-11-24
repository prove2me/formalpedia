-- Prove2me | Theorems.Thm_WilliamsonShmoys_RAMSpec_seq
-- name    : WilliamsonShmoys.RAMSpec.seq
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T06:02:55.834135+00:00
-- url     : https://prove2.me/theorems/04501f8c-1af5-4959-bf1e-fbc0e858a79b
-- title:
--   Sequencing rule for timed triples
-- statement:
--   If $\{P\}\,p\,\{Q\}_{\le t_1}$ and $\{Q\}\,p\,\{R\}_{\le t_2}$, then
--
--   $$\{P\}\;p\;\{R\}_{\le t_1+t_2}.$$
--
--   This is the composition rule for consecutive code fragments of one program; the costs add.
--
--   **Formalization Note.** $\mathrm{run}_p(s,t)$ is `planarRAMRun p s t`, the $t$-fold iterate of `planarRAMStep p`; triples are `RAMSpec` from `Def_WilliamsonShmoys_RAMSpec`.
-- source:
--   Program-logic infrastructure for the RAM model of Williamson–Shmoys, The Design of Approximation Algorithms, Theorem 10.11 (mission formalization)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.RAMSpec.seq (program : List PlanarRAMInstruction) (P Q R : PlanarRAMState → Prop)
    (t₁ t₂ : ℕ) (h₁ : RAMSpec program P Q t₁) (h₂ : RAMSpec program Q R t₂) :
    RAMSpec program P R (t₁ + t₂) := by sorry
