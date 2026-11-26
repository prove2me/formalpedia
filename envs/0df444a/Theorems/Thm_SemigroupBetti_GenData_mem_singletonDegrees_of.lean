-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_mem_singletonDegrees_of
-- name    : SemigroupBetti.GenData.mem_singletonDegrees_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:07:05.973397+00:00
-- url     : https://prove2.me/theorems/2eb863e5-4159-5081-96d5-eb39a034f18e
-- title:
--   Gen Data: mem singleton Degrees of
-- statement:
--   Every contributing degree with a singleton-support component lies in `𝓢`
--   (the cutoff is harmless by Lemma 0A).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L259-L261
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L259-L261

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.mem_singletonDegrees_of {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    d ∈ G.singletonDegrees := by sorry
