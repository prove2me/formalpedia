-- Prove2me | Theorems.Thm_PendantArcComplementConnected
-- name    : PendantArcComplementConnected
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T18:54:55.634375+00:00
-- url     : https://prove2.me/theorems/a7677c92-eaa6-4747-843b-09380f6c6bf9
-- title:
--   Adding a pendant polygonal arc preserves complement connectivity
-- statement:
--   Let $K$ be a compact subset of the Euclidean plane whose complement is polygonally path connected, and let $\gamma$ be a polygonal arc. If the carrier of $\gamma$ meets $K$ in exactly one endpoint and its other endpoint is outside $K$, then adding the arc preserves polygonal path connectedness of the complement:\n\n$$\n\operatorname{PolygonallyPathConnected}(K^{\mathrm c})\ \Longrightarrow\n\operatorname{PolygonallyPathConnected}\bigl((K\cup\operatorname{carrier}(\gamma))^{\mathrm c}\bigr).\n$$\n\nThe result is the topological induction step used when a leaf edge is attached to a crossing-free tree drawing.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PendantArcComplementConnected.lean#L1-L89

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

-- [TABLET NODE: PendantArcComplementConnected]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PendantArcComplementConnected.lean#L1-L89

lemma PendantArcComplementConnected (K : Set (EuclideanSpace ℝ (Fin 2)))
    (γ : PolygonalArc) :
    IsCompact K →
      PolygonallyPathConnected Kᶜ →
        ((γ.carrier ∩ K = ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            γ.target ∉ K) ∨
          (γ.carrier ∩ K = ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            γ.source ∉ K)) →
          PolygonallyPathConnected (K ∪ γ.carrier)ᶜ := by sorry
