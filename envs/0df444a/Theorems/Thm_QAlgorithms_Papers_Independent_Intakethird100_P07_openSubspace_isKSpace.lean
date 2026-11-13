-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_openSubspace_isKSpace
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.openSubspace_isKSpace
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T23:11:06.651886+00:00
-- url     : https://prove2.me/theorems/b1a50686-209f-4b7c-9b99-98b8495e6d8e
-- title:
--   Lemma B.11 — open subspaces of compactly generated spaces
-- statement:
--   Every open subspace A of a compactly generated space X is compactly generated: $$A\subseteq X\text{ open},\quad X\in kTop\quad\Longrightarrow\quad A\in kTop.$$ The topology on A is the ordinary subspace topology. Both X and its compact Hausdorff probes live in the same arbitrary universe. No separation assumption is imposed on X. This is the open-subspace foundation for preservation of open embeddings by kification.
-- source:
--   Martin Fuchssteiner, Cohomology of Local Cochains, arXiv:1110.2661v2, https://arxiv.org/pdf/1110.2661v2, Lemma B.11, PDF p.37.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.Topology.Compactness.LocallyCompact
set_option autoImplicit false
open CategoryTheory Topology TopologicalSpace
noncomputable section
universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P07
theorem openSubspace_isKSpace (X : Type u) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] (A : Set X) (hA : IsOpen A) :
    UCompactlyGeneratedSpace.{u} A := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P07
