-- Prove2me | Theorems.Thm_SP4TauCeti_HEP_isClosed
-- name    : SP4TauCeti.HEP_isClosed
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T14:19:01.900636+00:00
-- url     : https://prove2.me/theorems/bdb92db1-9f2a-428a-9589-c04d22bb1e97
-- title:
--   A HEP subset of a Hausdorff space is closed (TauCeti)
-- statement:
--   In a Hausdorff space, a subset with the homotopy extension property is closed. TauCeti proves this by identifying the subset as the fixed-point set of the retraction on the cylinder supplied by HEP. The cylinder-retraction/NDR-pair machinery is not available in Mathlib, so only the statement is transplanted.
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

variable {X : Type u} [TopologicalSpace X] [T2Space X] {A : Set X}

/-- In a Hausdorff space a subset with the homotopy extension property is closed (TauCeti,
`HasHomotopyExtensionProperty.isClosed`).  It is the set of points at which the cylinder
retraction supplied by HEP fixes `(1, x)`, hence closed.

TauCeti proves this from the retraction characterisation of HEP; that machinery is absent from
Mathlib, so only the statement is transplanted. -/
theorem HEP_isClosed (h : HasHomotopyExtensionProperty A) : IsClosed A := by
  sorry

end SP4TauCeti
