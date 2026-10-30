-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_prir_existence
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.prir_existence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:59:11.195073+00:00
-- url     : https://prove2.me/theorems/3dab599a-3699-4db2-afb8-cabd18c8b3e4
-- title:
--   Unnumbered PRIR existence, Eq.(42)
-- statement:
--   Let $R$ be an arbitrary unitary realization of the irreducible representation $\mu$ of $S_q$, where $q\ge1$. Let $\alpha\nearrow\mu$ denote all predecessor diagrams of size $q-1$, without a physical height restriction. Let $P_\alpha$ be the subgroup character projector and $C_\lambda$ the scalar of the sum of all transpositions in the irrep $\lambda$ (zero for an empty class). There exists a unitary coordinate map $U$ from the direct sum of predecessor Specht spaces onto the realization space such that
--
--   $$R(\pi)U=U\left(\bigoplus_{\alpha\nearrow\mu}\varphi^\alpha(\pi)\right)\qquad(\pi\in S_{q-1}).$$
--
--   The target Specht actions are computed in orthonormal bases of actual Young ideals. This constructs a partially reduced basis; no subsequent sum identity is part of the premise.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 17, Unnumbered PRIR existence, Eq.(42)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.17–18 Eq.(42): arbitrary unitary irrep has a unitary
multiplicity-free predecessor basis; no physical height restriction. -/
theorem prir_existence {r D : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (hR : RealizesSpechtIrrep mu R) :
    ∃ B : EuclideanSpace ℂ ((a : Preds mu) × Fin (sdim a.val)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin D),
      ∀ pi v, act (R (extendPerm pi) : Matrix (Fin D) (Fin D) ℂ) (B v) =
        B (predecessorAction mu pi v) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
