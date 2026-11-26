-- Prove2me | Theorems.Thm_SP4TauCeti_exists_continuousMap_prod_skeletonLT_succ
-- name    : SP4TauCeti.exists_continuousMap_prod_skeletonLT_succ
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T14:18:56.72775+00:00
-- url     : https://prove2.me/theorems/3268f001-a685-4b24-8f54-d7c0aa749af7
-- title:
--   Glue maps over closed n-cells to the (n+1)-skeleton (TauCeti)
-- statement:
--   This is TauCeti's `exists_continuousMap_prod_skeletonLT_succ`. Let $G$ be a map on $Z\times \operatorname{skeletonLT}\mathcal{C}\,n$, and for each $n$-cell $j$ let $K_j$ be a map on $Z\times \overline{B}^n$, agreeing with $G$ on the boundary sphere through the characteristic map of $j$. Then these maps glue to a continuous map on $Z\times \operatorname{skeletonLT}\mathcal{C}\,(n+1)$ restricting to $G$ and to each $K_j$. TauCeti proves continuity using its quotient-map description of the weak topology; only the statement is transplanted here.
-- source:
--   TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_continuousMap_prod_skeletonLT_succ and TauCeti.hasHomotopyExtensionProperty_skeletonLT (https://github.com/TauCetiProject/TauCeti); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1, proofs of Lemma 4.6 and Theorem 4.8.

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

set_option autoImplicit false

open scoped ContinuousMap unitInterval
open ContinuousMap Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [LocallyCompactSpace Z]

variable {n : ℕ}

/-- **Extension over the closed `n`-cells** (TauCeti, `exists_continuousMap_prod_skeletonLT_succ`).
A map `G` on `Z × skeletonLT C n` and maps `K j` on `Z × closedBall 0 1`, one for each `n`-cell
`j`, that agree with `G` on `Z × sphere 0 1` through the characteristic map of `j`, glue to a
continuous map on `Z × skeletonLT C (n + 1)` that restricts to `G` and, through each
characteristic map, to `K j`.

TauCeti proves continuity of the glued map with its quotient-map description of the weak
topology (`continuous_prod_complex_iff`), machinery absent from Mathlib; only the statement is
transplanted.  The closed-cell conclusion is written with Mathlib's
`closedCell_subset_skeletonLT`, equivalent to TauCeti's `map_mem_skeletonLT_succ`. -/
theorem exists_continuousMap_prod_skeletonLT_succ
    (G : C(Z × (skeletonLT C n : Set X), Y))
    (K : cell C n → C(Z × closedBall (0 : Fin n → ℝ) 1, Y))
    (hK : ∀ j z (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
      K j (z, y) = G (z, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩)) :
    ∃ F : C(Z × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), Y),
      (∀ z (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F (z, ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩) = G (z, ⟨x, hx⟩)) ∧
      ∀ j z (y : closedBall (0 : Fin n → ℝ) 1),
        F (z, ⟨map n j y, by
          simpa [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 by norm_num] using
            (closedCell_subset_skeletonLT n j (by exact ⟨y, y.property, rfl⟩))⟩) = K j (z, y) := by
  sorry

end SP4TauCeti
