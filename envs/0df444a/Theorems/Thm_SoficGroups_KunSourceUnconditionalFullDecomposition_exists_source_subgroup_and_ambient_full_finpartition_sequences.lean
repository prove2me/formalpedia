-- Prove2me | Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_subgroup_and_ambient_full_finpartition_sequences
-- name    : SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_subgroup_and_ambient_full_finpartition_sequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/cc59a931-dd64-4abc-8cd8-a1553374f49f
-- title:
--   SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_subgroup_and_ambient_full_finpartition_sequences
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSourceUnconditionalFullDecomposition
open Filter Topology

theorem SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_subgroup_and_ambient_full_finpartition_sequences
    {G Γ : Type} [Group G] [Group Γ]
    [DecidableEq G] [DecidableEq Γ]
    (A : SoficGroups.SoficApproximation G)
    (f : Γ →* G) (hf : Function.Injective f)
    (PΓ : SoficGroups.KazhdanPair.{0, 0} Γ)
    (PG : SoficGroups.KazhdanPair.{0, 0} G)
    (SΓ : Finset Γ) (SG : Finset G)
    (honeΓ : 1 ∈ SΓ) (honeG : 1 ∈ SG)
    (hcoverΓ : PΓ.generators ⊆ SΓ)
    (hcoverG : PG.generators ⊆ SG)
    (hsymmetricΓ : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesΓ : Subgroup.closure (SΓ : Set Γ) = ⊤)
    (hgeneratesG : Subgroup.closure (SG : Set G) = ⊤) :
    ∃ (γΓ γG : ℝ)
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by sorry
