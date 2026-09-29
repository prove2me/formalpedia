-- Prove2me | Theorems.Thm_WhitneyEmbedding_proper_injective_is_embedding
-- name    : WhitneyEmbedding.proper_injective_is_embedding
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T11:49:29.779745+00:00
-- url     : https://prove2.me/theorems/41ce6b75-f2d1-41f9-a5fc-b1b682b212c8
-- title:
--   Proper injective maps are embeddings
-- statement:
--   Let $X$ and $Y$ be topological spaces, where $Y$ is locally compact and Hausdorff. If $f : X 	o Y$ is a continuous map that is both proper (the preimage of every compact set is compact) and injective, then $f$ is a topological embedding.
--
--   A proper map into a locally compact Hausdorff space is automatically a closed map. Since $f$ is continuous, injective, and closed, it is a closed embedding, which implies that it is a homeomorphism onto its image. This is a fundamental result in point-set topology used to upgrade proper injective immersions into smooth embeddings.
-- source:
--   Standard point-set topology. See, for example, Bourbaki, General Topology, Chapter I, §10.

import Mathlib
open Function Filter Module Set Topology

theorem WhitneyEmbedding.proper_injective_is_embedding {X Y : Type*} 
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] 
    {f : X → Y} (hf_proper : IsProperMap f) (hf_inj : Injective f) :
    IsEmbedding f := by sorry
