-- Prove2me | Theorems.Thm_TopCat_Sheaf_surjective_global_sections_restrict_closed_of_connected_specializations
-- name    : TopCat.Sheaf.surjective_global_sections_restrict_closed_of_connected_specializations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T05:32:12.268188+00:00
-- url     : https://prove2.me/theorems/10f1f0af-6350-4dff-b2d9-9ab1ebd07434
-- title:
--   Lifting global sheaf sections from a closed subset of a spectral space
-- statement:
--   Let Z be closed in a spectral space X. Suppose the intersection of Z with each point closure in X is nonempty and connected. For any sheaf of sets on X, every global section of its inverse image on Z lifts to a global section on X.
-- source:
--   Stacks Project, Lemma 59.82.4, https://stacks.math.columbia.edu/tag/09ZG.

import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify

set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace
universe u

theorem TopCat.Sheaf.surjective_global_sections_restrict_closed_of_connected_specializations {X : TopCat.{u}} [SpectralSpace X]
    (F : TopCat.Sheaf (Type u) X) (Z : Set X) (hZ : IsClosed Z)
    (hConn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom.app
        (op (⊤ : Opens X))) := by sorry
