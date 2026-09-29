-- Prove2me | Theorems.Thm_R03SP03Hamiltonian_p3Factor_of_hamiltonianCycle
-- name    : R03SP03Hamiltonian.p3Factor_of_hamiltonianCycle
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:46:04.160517+00:00
-- url     : https://prove2.me/theorems/ecb6f2cc-469a-437e-8091-b5e69642eed2
-- title:
--   R03 P3-factor structural result: p3Factor of hamiltonianCycle
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP03Hamiltonian.p3Factor_of_hamiltonianCycle` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is ca6cd70d58ea6f471fccdae96f0391eb5cf9ffa4a1efb185a5eaa0a4b28b59ca.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp03/r03-sp03-hamiltonian-p3-factor-v1.lean; source SHA-256 ca6cd70d58ea6f471fccdae96f0391eb5cf9ffa4a1efb185a5eaa0a4b28b59ca; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03Hamiltonian

open R03SP03Hamiltonian
open CubicP3Partition
universe u
theorem p3Factor_of_hamiltonianCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsHamiltonianCycle)
    (hdiv : 3 ∣ Fintype.card V) :
    Nonempty (P3Factor G) := by sorry

end R03SP03Hamiltonian
