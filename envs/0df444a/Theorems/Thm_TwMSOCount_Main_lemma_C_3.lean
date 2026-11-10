-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_C_3
-- name    : TwMSOCount.Main.lemma_C_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:48:13.394883+00:00
-- url     : https://prove2.me/theorems/5d130f58-b4f3-4977-9c29-0c41b9b7a6b2
-- title:
--   Lemma C.3 — finitely many rank-$q$ types, with a computable bound and computable codes
-- statement:
--   For a color set $C=\{0,\dots,r-1\}$, a boundary-label set $B\subseteq\Lambda_k$ and a rank $q$, the rank-$q$ type of a colored $B$-boundaried graph is the set of sentences over $V_{C,B}$ of quantifier rank at most $q$ that it satisfies (Definition C.2).
--
--   **Lemma.** For fixed vocabulary, boundary labels and rank, the number of types has a computable finite bound: there is a computable $g$ with
--   $$\#\{\mathrm{tp}_{q,B}(H) : H \text{ a colored } B\text{-boundaried graph}\}\le g(r,|B|,q).$$
--   The type of a supplied finite graph has a computable code, and two such codes are equal exactly when the types agree.
--
--   Differences from the source:
--   - encoding: a computable bound for fixed vocabulary, boundary labels and rank → a computable g(r, |B|, q); reason: the number of types is invariant under renaming the labels, so it depends on B only through |B|
--   - encoding: a supplied finite graph → a GCode (vertex count, edges, colors, labelled vertices) decoded by decodeG; reason: every finite boundaried graph is isomorphic to a decoded code
--   - generalization: finite colored boundaried structures with injective boundary maps and nonempty C → the finite-type bound also covers r = 0 and noninjective boundary maps, and the code comparison covers every decoded GCode; reason: the finite-type recursion works for arbitrary interpretations of the finitely many constants, including coincident interpretations; every source graph is included
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma C.3, p. 28 (PDF 29)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables
import Definitions.Def_TwMSOCount_Main_Types

namespace TwMSOCount.Main

theorem lemma_C_3 :
    (∃ g : ℕ × ℕ × ℕ → ℕ, Computable g ∧
      ∀ (r k q : ℕ) (B : Finset (Lab k)),
        {T : Set (Formula r (Lab k)) | ∃ H : BGraph r k, H.B = B ∧ tp q H = T}.Finite ∧
        {T : Set (Formula r (Lab k)) | ∃ H : BGraph r k, H.B = B ∧ tp q H = T}.ncard ≤
          g (r, B.card, q)) ∧
    (∃ code : (ℕ × ℕ × ℕ) × GCode → ℕ, Computable code ∧
      ∀ (r k q : ℕ) [NeZero r] (x y : GCode),
        code ((r, k, q), x) = code ((r, k, q), y) ↔
          tp q (decodeG r k x) = tp q (decodeG r k y)) := by sorry

end TwMSOCount.Main
