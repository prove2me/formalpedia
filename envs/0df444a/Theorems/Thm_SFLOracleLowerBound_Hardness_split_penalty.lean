-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_split_penalty
-- name    : SFLOracleLowerBound.Hardness.split_penalty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:29:01.479223+00:00
-- url     : https://prove2.me/theorems/0107a63d-e646-4649-8e6c-f67b94123671
-- title:
--   Lemma 11 — Split penalty
-- statement:
--   Let $P_i$ be the orbits of a permutation group on a finite ground set. The split penalty
--   $$\psi(S)=\sum_i\min\{|S\cap P_i|,|P_i\setminus S|\}$$
--   is normalized and submodular. This is the cost term that measures splitting of the symmetry orbits in the replicated construction.
--
--   Differences from the source:
--   - encoding: finite ground sets and their subsets → finite types and Finset subsets; reason: bijections preserve every subset, cardinality and set operation
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 11, p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Replication

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 11, p.10. -/

theorem split_penalty {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (hΓ : PermutationGroup Γ) :
    Normalized (splitPenalty Γ) ∧ NonmonotoneSubmod.Shared.Submodular (splitPenalty Γ) := by sorry

end SFLOracleLowerBound.Hardness
