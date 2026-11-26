-- Prove2me | Theorems.Thm_SP4TauCeti_hasHomotopyExtensionProperty_skeletonLT
-- name    : SP4TauCeti.hasHomotopyExtensionProperty_skeletonLT
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T14:19:03.558288+00:00
-- url     : https://prove2.me/theorems/07cecf80-92a0-5fd0-8136-44a1a59e7f71
-- title:
--   Skeleta of relative CW complexes have HEP (TauCeti)
-- statement:
--   Every skeleton of a relative CW complex has the homotopy extension property inside the complex. Here the subset of $\mathcal{C}$ is the preimage of $\operatorname{skeletonLT}\mathcal{C}\,k$ under the inclusion $\mathcal{C}\hookrightarrow X$. TauCeti proves this inductively using the sphere-in-closed-ball HEP and its gluing theorem for the weak topology; those ingredients are absent from Mathlib, so only the statement is transplanted.
-- source:
--   TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_continuousMap_prod_skeletonLT_succ and TauCeti.hasHomotopyExtensionProperty_skeletonLT (https://github.com/TauCetiProject/TauCeti); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1, proofs of Lemma 4.6 and Theorem 4.8.

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4TauCetiHEP

set_option autoImplicit false

open scoped ContinuousMap unitInterval
open ContinuousMap Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- **Every skeleton of a relative CW complex has the homotopy extension property inside the
complex** (TauCeti, `hasHomotopyExtensionProperty_skeletonLT`).  Here the subset of `C` is the
preimage of `skeletonLT C k` under the inclusion `C ↪ X`.

TauCeti proves this by solving the extension problem on successive skeleta using the sphere-in-
closed-ball HEP and gluing with the quotient-map description of the weak topology; the NDR-pair
and cell-extension machinery is absent from Mathlib, so only the statement is transplanted. -/
theorem hasHomotopyExtensionProperty_skeletonLT (k : ℕ) :
    HasHomotopyExtensionProperty (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C) := by
  sorry

end SP4TauCeti
