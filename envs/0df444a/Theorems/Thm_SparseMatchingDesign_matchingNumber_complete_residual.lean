-- Prove2me | Theorems.Thm_SparseMatchingDesign_matchingNumber_complete_residual
-- name    : SparseMatchingDesign.matchingNumber_complete_residual
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:49.433427+00:00
-- url     : https://prove2.me/theorems/0660d8dc-9e07-42ed-983e-7c8c4d73dc82
-- title:
--   Proof of Lemma 1 — $\mu(\widetilde K_n)=\lfloor|\widetilde K_n|/2\rfloor$
-- statement:
--   Let $S\subseteq[n]$ be the set of surviving nodes and $\widetilde K_n$ the residual complete graph, the complete graph on $S$. Then
--   $$\mu(\widetilde K_n)=\Big\lfloor \frac{|\widetilde K_n|}{2}\Big\rfloor=\begin{cases}|\widetilde K_n|/2 & \text{if } |\widetilde K_n| \text{ is even},\\ (|\widetilde K_n|-1)/2 & \text{if } |\widetilde K_n| \text{ is odd}.\end{cases}$$
--   It identifies the matching number of the input graph's residual, against which the $K$-ring is compared in Claim EC.4.
--
--   Differences from the source:
--   - encoding: the random residual complete graph K̃ₙ → (⊤ : SimpleGraph (Fin n)).induce S for every surviving set S; reason: the identity holds pointwise for every realisation
--   - encoding: ⌊|K̃ₙ|/2⌋ and the two parity cases → natural-number division S.card / 2, and the two cases as real equalities; reason: ℕ division is the floor; the cases are stated in ℝ to avoid truncated subtraction
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), proof of Lemma 1 (§EC.2), p.ec4, first display (pdf p.47)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

namespace SparseMatchingDesign

/-- A residual graph of the complete graph `Kₙ` on `s` surviving nodes has matching number
`⌊s/2⌋`: `s/2` if `s` is even and `(s − 1)/2` if `s` is odd.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), proof of Lemma 1 (§EC.2), p.ec4, first display: "Since any residual subgraph of a complete
graph is complete, we have μ(K̃ₙ) = ⌊|K̃ₙ|/2⌋ = |K̃ₙ|/2 if |K̃ₙ| is an even number;
(|K̃ₙ| − 1)/2 if |K̃ₙ| is an odd number."

**Formalization Note** The residual graph for the surviving set `S` is `(⊤ : SimpleGraph (Fin n)).induce S`,
so `|K̃ₙ| = S.card`. μ is `TuranMatching.Clique.matchingNumber`. The floor is natural-number
division `S.card / 2`; the two cases are stated in `ℝ`. The statement holds for every `S`,
so no probability is involved. -/
theorem matchingNumber_complete_residual (n : ℕ) (S : Finset (Fin n)) :
    TuranMatching.Clique.matchingNumber ((⊤ : SimpleGraph (Fin n)).induce (S : Set (Fin n))) =
        S.card / 2 ∧
    (Even S.card →
      (TuranMatching.Clique.matchingNumber ((⊤ : SimpleGraph (Fin n)).induce (S : Set (Fin n))) : ℝ) =
        (S.card : ℝ) / 2) ∧
    (Odd S.card →
      (TuranMatching.Clique.matchingNumber ((⊤ : SimpleGraph (Fin n)).induce (S : Set (Fin n))) : ℝ) =
        ((S.card : ℝ) - 1) / 2) := by sorry

end SparseMatchingDesign
