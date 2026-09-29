-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_lemma3_three_way_split
-- name    : PaigeTarjan.Coarsest.lemma3_three_way_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:50:44.8648+00:00
-- url     : https://prove2.me/theorems/c7dfddc1-e47a-4396-91ca-00ed9f08acd9
-- title:
--   Lemma 3, p. 980 — the three-way split of a block D into D₁₁, D₁₂ and D₂
-- statement:
--   Let $E$ be a relation on a finite set $U$ and let $Q$ be a partition of $U$ that is stable with respect to a set $S$ which is a union of some of the blocks of $Q$. Let $B \in Q$ be a block with $B \subseteq S$, and refine $Q$ first with respect to $B$ and then with respect to $S - B$. For a block $D \in Q$ put
--   $$D_1 = D \cap E^{-1}(B),\quad D_2 = D - D_1,\quad D_{11} = D_1 \cap E^{-1}(S - B),\quad D_{12} = D_1 - D_{11}.$$
--   Then:
--
--   1. refining $Q$ with respect to $B$ splits $D$ into the two blocks $D_1$ and $D_2$ if and only if $D \cap E^{-1}(B) \neq \emptyset$ and $D - E^{-1}(B) \neq \emptyset$;
--   2. refining $\mathrm{split}(B, Q)$ with respect to $S - B$ splits $D_1$ into the two blocks $D_{11}$ and $D_{12}$ if and only if $D_1 \cap E^{-1}(S - B) \neq \emptyset$ and $D_1 - E^{-1}(S - B) \neq \emptyset$;
--   3. refining $\mathrm{split}(B, Q)$ with respect to $S - B$ does not split $D_2$;
--   4. $D_{12} = D_1 \cap \bigl(E^{-1}(B) - E^{-1}(S - B)\bigr)$.
--
--   Identity 4 is the observation behind the efficient implementation: the three-way split of $D$ into $D_{11}$, $D_{12}$ and $D_2$ can be computed by scanning only the preimages of elements of the smaller set $B$.
--
--   **Formalization Note** "Refining splits a block $D$ into $D'$ and $D''$" is encoded as: $D$ is not a block of the refined partition, while $D'$ and $D''$ are. "Does not split $D_2$" is encoded as: if $D_2$ is a block of $\mathrm{split}(B,Q)$, it is still a block after refining with respect to $S - B$.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 980, Lemma 3

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- Lemma 3, p. 980. Let `Q` be a partition stable with respect to a set `S` that is a union of
some of the blocks of `Q`, let `B ∈ Q` with `B ⊆ S`, and refine `Q` first with respect to `B`
and then with respect to `S − B`. For a block `D ∈ Q` put `D₁ = D ∩ E⁻¹(B)`, `D₂ = D − D₁`,
`D₁₁ = D₁ ∩ E⁻¹(S − B)`, `D₁₂ = D₁ − D₁₁`. Then
(1) refining `Q` with respect to `B` splits `D` into `D₁` and `D₂` iff `D ∩ E⁻¹(B) ≠ ∅` and
`D − E⁻¹(B) ≠ ∅`;
(2) refining `split(B, Q)` with respect to `S − B` splits `D₁` into `D₁₁` and `D₁₂` iff
`D₁ ∩ E⁻¹(S − B) ≠ ∅` and `D₁ − E⁻¹(S − B) ≠ ∅`;
(3) refining `split(B, Q)` with respect to `S − B` does not split `D₂`;
(4) `D₁₂ = D₁ ∩ (E⁻¹(B) − E⁻¹(S − B))`.
"Refining splits block `D` into `D′` and `D″`" is read as: `D` is not a block of the result, and
`D′` and `D″` are. -/
theorem lemma3_three_way_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S B D : Finset U)
    (hQ : IsPartition Q) (hSQ : IsUnionOfBlocks S Q) (hstab : StableWrt E Q S)
    (hB : B ∈ Q) (hBS : B ⊆ S) (hD : D ∈ Q) :
    let D₁ := D ∩ preimage E B
    let D₂ := D \ D₁
    let D₁₁ := D₁ ∩ preimage E (S \ B)
    let D₁₂ := D₁ \ D₁₁
    ((D ∉ split E B Q ∧ D₁ ∈ split E B Q ∧ D₂ ∈ split E B Q) ↔
        ((D ∩ preimage E B).Nonempty ∧ (D \ preimage E B).Nonempty)) ∧
    ((D₁ ∉ split E (S \ B) (split E B Q) ∧ D₁₁ ∈ split E (S \ B) (split E B Q) ∧
        D₁₂ ∈ split E (S \ B) (split E B Q)) ↔
        ((D₁ ∩ preimage E (S \ B)).Nonempty ∧ (D₁ \ preimage E (S \ B)).Nonempty)) ∧
    (D₂ ∈ split E B Q → D₂ ∈ split E (S \ B) (split E B Q)) ∧
    D₁₂ = D₁ ∩ (preimage E B \ preimage E (S \ B)) := by sorry

end PaigeTarjan.Coarsest
