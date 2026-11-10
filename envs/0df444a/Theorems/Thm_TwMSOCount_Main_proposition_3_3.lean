-- Prove2me | Theorems.Thm_TwMSOCount_Main_proposition_3_3
-- name    : TwMSOCount.Main.proposition_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:18.109215+00:00
-- url     : https://prove2.me/theorems/81a6a839-92b5-4c53-bb54-b8ad1537d7ca
-- title:
--   Proposition 3.3 — computable MSO2 sentences $\Phi_{B,B_S,N}$ recognize the canonical description on the candidate parent
-- statement:
--   For $B\subseteq\Lambda_k$, $B_S\subseteq B$ and nonempty $N\subseteq\Lambda_k\setminus B$, consider candidate assemblies (§3.2) with these labels and their candidate parents $(H,\chi,\iota)$; $\iota^+$ is the boundary map on $B\cup N$ before $N$ is forgotten.
--
--   **Proposition.** From $k$ one can compute MSO2 sentences $\Phi_{B,B_S,N}$ over $V_{C,B\cup N}$ for all such $B, B_S, N$, with the following property. Consider a valid candidate assembly with these labels and parent $(H,\chi,\iota)$, where $\mathrm{tw}(H)\le k$ and $|B|\le 6(k+1)$. Assume that the assembly follows the naming and ordering conventions of Section 3.1 and that $\iota^+(s_1) = \min H^\circ$ for $s_1 = \min N$. Then
--   $$I(H,\chi,\iota^+)\models\Phi_{B,B_S,N}\iff\text{the assembly is the canonical description of } H .$$
--
--   This is what lets the dynamic program check, on a finite summary of the candidate parent, that it is counting the canonical description and no other.
--
--   **Formalization Note.** "One can compute" is a computable map $\Phi_c$ from $(k,B,B_S,N)$ (label sets as increasing index lists) to the prefix codes of the sentences; the sentences use no color predicate, so one family serves every color set.
--
--   Differences from the source:
--   - encoding: from k one can compute sentences Φ_{B,B_S,N} → ∃ Φ and a Computable Φc with encode (Φ r k B B_S N) = Φc (k, B, B_S, N), Φ a sentence with constants in B ∪ N; reason: Mathlib computability on codes; the code does not depend on the color set
--   - encoding: a candidate assembly with these labels and parent (H, χ, ι) → an `Assembly` record with `Valid`, its `parent` and `parentExt` (carrying ι⁺); reason: the record of §3.2 with the conditions each piece must satisfy
--   - encoding: the assembly is the canonical description of H → IsCanonDesc: separator S⋆(H, B), pattern of E(H[S⋆]), naming convention, and pieces equal in anchor order up to isomorphism preserving colors, boundary labels and output labels; reason: the description of H along S⋆ is defined by these data
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Proposition 3.3, p. 7 (PDF 8); Appendix C.2, pp. 25–27 (PDF 26–28)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

namespace TwMSOCount.Main

theorem proposition_3_3 :
    ∃ (Φc : ℕ × List ℕ × List ℕ × List ℕ → List ℕ)
      (Φ : ∀ r k : ℕ, Finset (Lab k) → Finset (Lab k) → Finset (Lab k) → Formula r (Lab k)),
      Computable Φc ∧
      (∀ (r k : ℕ) (B BS N : Finset (Lab k)), BS ⊆ B → N.Nonempty → Disjoint N B →
        (Φ r k B BS N).IsSentence ∧ (Φ r k B BS N).consts ⊆ B ∪ N ∧
        (Φ r k B BS N).encode (fun b => b.val) =
          Φc (k, (B.sort (· ≤ ·)).map Fin.val, (BS.sort (· ≤ ·)).map Fin.val,
            (N.sort (· ≤ ·)).map Fin.val)) ∧
      ∀ (r k : ℕ) (A : Assembly r k), A.Valid → A.N.Nonempty →
        A.parent.tw ≤ k → A.B.card ≤ 6 * (k + 1) → A.FollowsConventions →
        (∃ s ∈ A.N, (∀ t ∈ A.N, s ≤ t) ∧
          ∃ h : s ∈ A.parentExt.B, IsXStar A.parent (A.parentExt.ι ⟨s, h⟩)) →
        (A.parentExt.Models (Φ r k A.B A.BS A.N) ↔ A.IsCanonDesc) := by sorry

end TwMSOCount.Main
