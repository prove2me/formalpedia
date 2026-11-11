-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_6_2
-- name    : ShortestPlanarDisjoint.Main.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:15.834963+00:00
-- url     : https://prove2.me/theorems/b045f587-892a-4a90-bb68-c7425e214da2
-- title:
--   Lemma 6.2 — Surface seams
-- statement:
--   For a connected nontrivial cellular embedding of Euler genus g_E with f used terminal faces and any selected boundary gaps, there are r=g_E+f−1 actual arcs with disjoint images and endpoints in those gaps whose cut is a disk. One absolute A bounds all graph-edge crossings by A(g_E+f)(n+g_E). The disk has f+2r=2g_E+3f−2 sides: one contiguous block per used face and two copies of every seam. Their equal or reversed boundary-order identification is determined by the disk parametrization. Both orientable and nonorientable embeddings are included.
--
--   Differences from the source:
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - encoding: proper surface arcs, their ordered crossings and a disk cut → finite rational polygonal curves on the flag-triangle realization, with RealizesCut and a uniform existential crossing coefficient; reason: polygonal representatives and parallel tracks give the same source arcs up to deformation without changing crossings or graph costs; side gluing is a conclusion, never an input cut certificate
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 6.2, p. 30 (PDF p. 32)

import Definitions.Def_ShortestPlanarDisjoint_Main_Seams
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Actual disk cuts for orientable and nonorientable cellular embeddings.
The same/reverse identification is determined by the two boundary traversals
in RealizesCut; no orientation of the surface is supplied or assumed. -/
theorem lemma_6_2 :
    ∃ A : ℕ, 0 < A ∧
      ∀ (n k g f : ℕ) (I : RoutingInput n k) (E : FaceInput I f) (gaps : E.GapChoice),
        0 < k → E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
        ∃ S : SeamCode E (g+f-1), S.RealizesCut gaps ∧
          S.crossingCount ≤ A * (g+f) * (n+g) ∧
          S.layout.sideOrder.length = f + 2 * (g+f-1) ∧
          S.layout.sideOrder.length = 2*g+3*f-2 := by sorry
end ShortestPlanarDisjoint.Main
