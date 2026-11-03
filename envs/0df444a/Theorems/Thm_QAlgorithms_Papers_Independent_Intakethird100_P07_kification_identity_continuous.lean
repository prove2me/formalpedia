-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_identity_continuous
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_identity_continuous
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:25:11.195212+00:00
-- url     : https://prove2.me/theorems/f24a22fa-467b-4ec2-bf5d-6eaedd45927c
-- title:
--   Lemma B.3
-- statement:
--   Let $X$ be any topological space. Give its underlying set the final topology for all continuous maps from compact Hausdorff spaces, and denote the resulting space by $kX$. Then
--
--   $$\operatorname{id}:kX\longrightarrow X\quad\text{is continuous}.$$
--
--   Thus the k-topology is finer than the given topology. No separation axiom on $X$ is imposed.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Lemma B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma B.3, PDF p. 36: kX→X is the continuous set-theoretic identity. -/
theorem kification_identity_continuous (X : Type u) [TopologicalSpace X] :
    Continuous (fun x : KSpace X => (x : X)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
