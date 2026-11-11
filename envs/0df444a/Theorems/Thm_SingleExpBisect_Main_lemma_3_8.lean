-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_8
-- name    : SingleExpBisect.Main.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:40:46.461282+00:00
-- url     : https://prove2.me/theorems/abd4bd9d-e337-4fb7-9064-0e206b5553e8
-- title:
--   Lemma 3.8 — monotonicity Φ_t(S') ⊆ Φ_t(S) for S' ⊆ S
-- statement:
--   For every graph $G$, $W\subseteq V(G)$ (playing $V(G_t)$) and $S'\subseteq S\subseteq W$: $\Phi_t(S')\subseteq\Phi_t(S)$.
--
--   Differences from the source:
--   - generalization: W = V(G_t) for a node of the Section 3 decomposition → any W ⊆ V(G); reason: the proof (p. 24) uses only submodularity and Lemma 3.7
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 24, Lemma 3.8

import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData

open scoped Classical

namespace SingleExpBisect.Main

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.4, p. 24, Lemma 3.8: if
`S′ ⊆ S ⊆ V(G_t)` then `Φ_t(S′) ⊆ Φ_t(S)` (`W = V(G_t)`). -/
theorem lemma_3_8 {n : ℕ} (G : SimpleGraph (Fin n)) (W S' S : Finset (Fin n)) (h' : S' ⊆ S)
    (hS : S ⊆ W) :
    Phi G W S' ⊆ Phi G W S := by sorry

end SingleExpBisect.Main
