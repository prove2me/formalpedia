-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_5
-- name    : ThreshRankBIS.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:04:45.148837+00:00
-- url     : https://prove2.me/theorems/6b99c90a-4be1-4494-8d6c-dff9441bca19
-- title:
--   Lemma 5 — cuts $S_A$ and maximal independent sets $M_A$
-- statement:
--   Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, let $0<\rho<1$ and let $U$ be the spectral subspace of $L_G=dI-A_G$ for the eigenvalues at most $\rho d$. For $A\subseteq X$ put $S_A=[A]\cup N(A)$ and $M_A=[A]\cup(Y\setminus N(A))$. Then:
--
--   1. the cut $S_A$ has
--   $$
--   |\nabla(S_A)|=\mathbf 1_{S_A}^{\mathsf T}L_G\mathbf 1_{S_A}=d\,t(A),\qquad \mathrm{dist}(\mathbf 1_{S_A},U)^2\le t(A)/\rho; \tag{6}
--   $$
--   2. $M_A$ is a maximal independent set, $|M_A|=n-t(A)$, and $M_A$ contains every independent set whose $X$-part is $A$;
--   3. every maximal independent set $I$ arises uniquely from its closed $X$-part: $I\cap X$ is closed and $I=M_{I\cap X}$, and distinct closed sets give distinct $M_A$.
--
--   This is the closure–cut correspondence: maximal independent sets of small deficit correspond to sparse cuts, whose indicators lie close to the low-dimensional subspace $U$.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - reading: every maximal independent set arises uniquely from its closed X-part → for every maximal independent I, I ∩ X is closed and M_{I∩X} = I; and A ↦ M_A is injective on closed sets; reason: this is the bijection between closed left sets and maximal independent sets that the sentence asserts
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 5, p.9, display (6)

import Mathlib
import Definitions.Def_ThreshRankBIS_closure
import Definitions.Def_ThreshRankBIS_hardcoreZ
import Definitions.Def_ThreshRankBIS_thresholdRank
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Lemma 5 (Cuts and maximal independent sets)**, p.9. For `A ⊆ X`, with
`S_A = [A] ∪ N(A)` and `M_A = [A] ∪ (Y ∖ N(A))`:
1. `|∇(S_A)| = 1_{S_A}ᵀ L_G 1_{S_A} = d·t(A)` and `dist(1_{S_A}, U)² ≤ t(A)/ρ` (display (6));
2. `M_A` is maximal independent, `|M_A| = n − t(A)`, and `M_A` contains every independent set
   whose `X`-part is `A`;
3. every maximal independent set `I` arises from its closed `X`-part: `I ∩ X` is closed and
   `I = M_{I ∩ X}`, and `A ↦ M_A` is injective on closed sets.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 5, p.9.

**Formalization Note.** `U` is `specSub ρ E d`, the spectral subspace of `L_G` for eigenvalues
`≤ ρd`; the quadratic form is `dotProduct` on `V n → ℝ`; `t(A)` and `|M_A| = n − t(A)` are
integers. -/
theorem lemma_5 {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ A : Finset (Fin n),
      (#(boundary E (SA E A)) : ℝ) =
          dotProduct (indE (SA E A)).ofLp ((lapMat E d).mulVec (indE (SA E A)).ofLp) ∧
        dotProduct (indE (SA E A)).ofLp ((lapMat E d).mulVec (indE (SA E A)).ofLp) =
          (d : ℝ) * (deficit E A : ℝ) ∧
        distU2 ρ E d (SA E A) ≤ (deficit E A : ℝ) / ρ ∧
        IsMaxIndep E (MA E A) ∧
        (#(MA E A) : ℤ) = (n : ℤ) - deficit E A ∧
        ∀ J : Finset (V n), IsIndep E J → leftPart J = A → J ⊆ MA E A) ∧
    (∀ I : Finset (V n), IsMaxIndep E I →
      IsClosedLeft E (leftPart I) ∧ MA E (leftPart I) = I) ∧
    (∀ A A' : Finset (Fin n), IsClosedLeft E A → IsClosedLeft E A' → MA E A = MA E A' →
      A = A') := by sorry

end ThreshRankBIS
