-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P32_cgLocallyShrinkable_isQuasiShrinkable
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P32.cgLocallyShrinkable_isQuasiShrinkable
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:46:11.666197+00:00
-- url     : https://prove2.me/theorems/920c8b4a-b3ab-47f0-884e-7fd283238aa5
-- title:
--   CG-local shrinkability implies quasi-shrinkability
-- statement:
--   Let $f:X\to B$ be a continuous map between compactly generated Hausdorff spaces. Suppose $f$ is shrinkable over every member of some $\mathcal{CG}$-cover of $B$. Then for every locally compact, paracompact Hausdorff space $T$ and every continuous map $g:T\to B$, the pullback projection is shrinkable:
--
--   $$X\times_B T\longrightarrow T.$$
--
--   The pullback has its Kelley-corrected topology. This is quasi-shrinkability in Definition 4.4; all three conditions on the test space are retained.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, PDF p. 28, Lemma 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- Lemma 4.10, PDF p.28: CG-local shrinkability implies quasi-shrinkability.
All locally compact, paracompact Hausdorff probes occur inside the conclusion;
no global shrinkability or numerable-cover conclusion is assumed. -/
theorem cgLocallyShrinkable_isQuasiShrinkable (X B : Type u)
    [TopologicalSpace X] [TopologicalSpace B] [T2Space X] [T2Space B]
    [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace B] (f : C(X, B))
    (hf : CGLocallyShrinkableMap f) : QuasiShrinkableMap f := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P32
