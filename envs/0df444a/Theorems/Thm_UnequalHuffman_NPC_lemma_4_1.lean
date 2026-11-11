-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_4_1
-- name    : UnequalHuffman.NPC.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:47:11.757779+00:00
-- url     : https://prove2.me/theorems/bb2500d0-140d-41d3-a473-3875dafffd22
-- title:
--   Lemma 4.1 (all clauses but polynomial time; companion lemma_4_1_polytime) — the second reduction preserves optima: OPT_code = β + OPT_tree
-- statement:
--   Let $I$ be a well-formed leaf-profile instance and $J$ the coding instance (13): frequencies $w_j = \Gamma 2^{H-d_j} + \theta_j$ and letter costs $(M, M+1)$. Then:
--
--   1. the frequencies are positive integers;
--   2. among all binary prefix codes, those of minimum weighted length $L$ are exactly those placing every symbol $j$ at depth $d_j$;
--   3. $\mathrm{OPT}_{\mathrm{tree}}(I)$ exists, and among the codes placing every symbol at its prescribed depth the minimum weighted number of ones is $B_0 + \mathrm{OPT}_{\mathrm{tree}}(I)$;
--   4. $\mathrm{OPT}_{\mathrm{code}}(J) = \beta + \mathrm{OPT}_{\mathrm{tree}}(I)$ (14);
--   5. every feasible tree $T$ has canonical codes, and every canonical code satisfies $\mathrm{cost}_{M,M+1}(C_T) = \beta + \mathrm{score}(T)$ (15), for every tie-breaking;
--   6. every canonical code of an optimal source tree is an optimal code;
--   7. the code tree of any optimal code is an optimal source tree.
--
--   The polynomial-time clause of the lemma is the companion item `lemma_4_1_polytime`.
--
--   Source (pp. 32–33): "Lemma 4.1. The frequencies in (13) are positive integers. The codes of minimum ordinary weighted length are exactly the codes placing every symbol $j$ at depth $d_j$. Among these codes, the minimum weighted number of ones is $B_0 + \mathrm{OPT}_{\mathrm{tree}}(I)$. With letter costs $(M, M+1)$, the optimum values satisfy $\mathrm{OPT}_{\mathrm{code}}(J) = \beta + \mathrm{OPT}_{\mathrm{tree}}(I)$. (14) For every source-feasible ordered tree $T$, $\mathrm{cost}(C_T) = \beta + \mathrm{score}(T)$. (15) The canonical map sends every optimal source tree to an optimal code. Conversely, forgetting the symbol labels of any optimal code yields an optimal source tree. The instance construction and both solution maps take polynomial time, and all constructed numbers have polynomial binary encoding length."
--
--   Differences from the source:
--   - encoding: the polynomial-time clause (last sentence) → the separate item lemma_4_1_polytime; reason: length of the statement; both items are planned to be proved and together state every clause
--   - encoding: OPT_tree(I), OPT_code(J) as minima → predicates IsOptTree I v and IsOptCodeValue (attained minimum); existence of OPT_tree stated as a clause; reason: avoids junk values of sInf; OPT_tree(I) = min presupposes the minimum exists
--   - encoding: symbols j(t, k), depths d_j, adjustments θ_j; frequencies (13) → 0-based symbol index into symDepths and theta (depth-major, rank order); freqZ in ℤ, the output frequencies freq = toNat of freqZ; reason: clause 1 makes toNat the identity on these values
--   - encoding: canonical code C_T, ties broken arbitrarily; forgetting the symbol labels → IsCanonicalCode: bijection of symbols onto leaves of T at the prescribed depths with coordinates nondecreasing in k, (15) for every such code; the forgotten-label tree is codeTree C; reason: every tie-breaking gives such a code and every such code is one tie-breaking
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 32–33, Lemma 4.1

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_SecondReduction

open FuchsThesis.Coding

namespace UnequalHuffman.NPC

open LPInstance

/-- Lemma 4.1 (pp. 32–33), all clauses except the polynomial-time clause (stated in
`lemma_4_1_polytime`). For a well-formed leaf-profile instance `I` and the coding instance `J`
of (13) (frequencies `w`, letter costs `(M, M + 1)`): the frequencies are positive integers; the
prefix codes of minimum weighted length are exactly those placing every symbol `j` at depth
`d_j`; `OPT_tree(I)` exists, and among the depth-`d` codes the minimum weighted number of ones is
`B₀ + OPT_tree(I)`; `OPT_code(J) = β + OPT_tree(I)` (14); every feasible tree `T` has canonical
codes and each satisfies `cost(C_T) = β + score(T)` (15); canonical codes of optimal trees are
optimal codes; and the tree of any optimal code is an optimal source tree. -/
theorem lemma_4_1 (I : LPInstance) (hI : I.IsValid) :
    (∀ x ∈ I.freqZ, 0 < x) ∧
    (∀ C : Fin I.freq.length → List Bool, IsInstantaneous C →
      (IsLengthOptimal I.freq C ↔ ∀ j, (C j).length = I.symDepths.getD j 0)) ∧
    (∃ v, I.IsOptTree v) ∧
    (∀ v, I.IsOptTree v →
      ((∃ C : Fin I.freq.length → List Bool, IsInstantaneous C ∧
          (∀ j, (C j).length = I.symDepths.getD j 0) ∧
          (weightedOnes I.freq C : ℤ) = I.B0 + v) ∧
        ∀ C : Fin I.freq.length → List Bool, IsInstantaneous C →
          (∀ j, (C j).length = I.symDepths.getD j 0) →
          I.B0 + v ≤ (weightedOnes I.freq C : ℤ)) ∧
      IsOptCodeValue I.bigM (I.bigM + 1) I.freq (I.beta + v)) ∧
    (∀ T : OTree, I.IsFeasibleTree T →
      (∃ C, I.IsCanonicalCode T C) ∧
      ∀ C, I.IsCanonicalCode T C →
        (cost I.bigM (I.bigM + 1) I.freq C : ℤ) = I.beta + I.score T) ∧
    (∀ T : OTree, I.IsOptimalTree T → ∀ C, I.IsCanonicalCode T C →
      IsCostOptimal I.bigM (I.bigM + 1) I.freq C) ∧
    (∀ C : Fin I.freq.length → List Bool, IsCostOptimal I.bigM (I.bigM + 1) I.freq C →
      I.IsOptimalTree (codeTree C)) := by sorry

end UnequalHuffman.NPC
