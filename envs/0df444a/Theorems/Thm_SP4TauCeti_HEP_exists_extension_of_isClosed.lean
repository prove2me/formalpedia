-- Prove2me | Theorems.Thm_SP4TauCeti_HEP_exists_extension_of_isClosed
-- name    : SP4TauCeti.HEP_exists_extension_of_isClosed
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T14:19:00.669003+00:00
-- url     : https://prove2.me/theorems/cbe1e786-f12d-5bf0-8ae7-86a480060ba3
-- title:
--   Closed HEP subsets extend homotopies in arbitrary universes (TauCeti)
-- statement:
--   For a closed subset $A\subseteq X$ with the homotopy extension property, every homotopy $I\times A\to Y$ whose initial map extends to $X$ extends to $I\times X\to Y$. The closedness hypotheses lets the argument pass through a retraction characterisation of HEP, which is universe-free; hence the target $Y$ may live in an arbitrary universe. TauCeti proves this via cylinder retractions; only the statement is transplanted here.
-- source:
--   TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_continuousMap_prod_skeletonLT_succ and TauCeti.hasHomotopyExtensionProperty_skeletonLT (https://github.com/TauCetiProject/TauCeti); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1, proofs of Lemma 4.6 and Theorem 4.8.

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4TauCetiHEP

set_option autoImplicit false

open scoped ContinuousMap unitInterval
open ContinuousMap Metric Set Topology Topology.RelCWComplex unitInterval

universe u v

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A closed subset with the homotopy extension property extends homotopies with values in a
space in an arbitrary universe (TauCeti, `HasHomotopyExtensionProperty.exists_extension_of_isClosed`).
The closedness hypothesis routes the argument through the retraction characterisation of HEP,
which is universe-free, while the defining quantifier of `HasHomotopyExtensionProperty` only
ranges over targets in the universe of `X`.

TauCeti proves this from the cylinder retraction of a closed HEP subset; the NDR-pair and
cylinder-retraction machinery is absent from Mathlib, so only the statement is transplanted. -/
theorem HEP_exists_extension_of_isClosed (hA : IsClosed A)
    (h : HasHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (H : C(I × A, Y)) (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  sorry

end SP4TauCeti
