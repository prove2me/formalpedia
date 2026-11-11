-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_7
-- name    : RandDelMatroid.Indep.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:32.847281+00:00
-- url     : https://prove2.me/theorems/414575ff-60f5-4226-88c7-2b0e21ea59d4
-- title:
--   Lemma 7 — unique projection of a circuit onto the decomposition tree
-- statement:
--   Let $T$ be an unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with matroid $M_u$ on $E_u$ at each node. Every circuit $C$ of $M$ admits a unique decomposition
--
--   $$C=\mathop{\triangle}_{u\in V(T)}C_u,$$
--
--   where each $C_u\subseteq E_u$ is empty or a circuit of $M_u$ (the **projection** of $C$ onto $u$), such that
--
--   1. for every edge $e=\{u,v\}$ of $T$, $C_u\cap S_e=C_v\cap S_e$ and $|C_u\cap S_e|=|C_v\cap S_e|\le1$;
--   2. the nodes with nonempty projections induce a connected subtree;
--   3. for every nonempty connected subtree $Q$, the set $C_Q=\triangle_{u\in V(Q)}C_u$ is empty or a circuit of $M_Q$.
--
--   The projections are how the proof of Lemma 15 reads a circuit of $M_{Q_u}$ at the node $u$.
--
--   **Formalization Note** Uniqueness is stated among all families $(D_u)$ of sets $D_u\subseteq E_u$, each empty or a circuit of $M_u$, with $C=\triangle_uD_u$ and property 1 (this is what the uniqueness argument of the proof uses); existence provides a family with properties 1–3.
--
--   Differences from the source:
--   - reading: 'admits a unique decomposition … satisfying the following properties' → existence of a family with properties 1–3; uniqueness among families of the stated form satisfying property 1; reason: the uniqueness proof (p. 15) uses only the boundary condition; uniqueness among this larger class implies uniqueness among families with 1–3
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), pp. 14–15, Lemma 7

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 7 (pp. 14–15). Let `T` be an unordered decomposition tree of a regular matroid `M`.
Every circuit `C` of `M` is `C = △_{u ∈ V(T)} C_u` for sets `C_u ⊆ E_u`, each empty or a circuit of
`M_u` (the projections of `C`), such that
1. on every tree edge `e = {u, v}`, `C_u ∩ S_e = C_v ∩ S_e` and `|C_u ∩ S_e| ≤ 1`;
2. the nodes with nonempty projections induce a connected subtree;
3. for every nonempty connected subtree `Q`, `C_Q = △_{u ∈ Q} C_u` is empty or a circuit of `M_Q`;
and the decomposition is unique: any family `(D_u)` of sets `D_u ⊆ E_u`, each empty or a circuit of
`M_u`, with `C = △_u D_u` and property 1, equals `(C_u)`. -/
theorem lemma_7 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsUnorderedDecompTree M T Mn) (C : Set β) (hC : M.IsCircuit C) :
    ∃ X : ι → Set β,
      (∀ u, X u ⊆ (Mn u).E ∧ (X u = ∅ ∨ (Mn u).IsCircuit (X u))) ∧
      C = bigSymmDiff Finset.univ X ∧
      (∀ u v, T.Adj u v → X u ∩ edgeBoundary Mn u v = X v ∩ edgeBoundary Mn u v ∧
        (X u ∩ edgeBoundary Mn u v).ncard ≤ 1) ∧
      (T.induce {u | (X u).Nonempty}).Connected ∧
      (∀ Q : Finset ι, IsConnectedSubtree T Q →
        bigSymmDiff Q X = ∅ ∨ (subtreeMatroid T Mn Q).IsCircuit (bigSymmDiff Q X)) ∧
      (∀ Y : ι → Set β, (∀ u, Y u ⊆ (Mn u).E ∧ (Y u = ∅ ∨ (Mn u).IsCircuit (Y u))) →
        C = bigSymmDiff Finset.univ Y →
        (∀ u v, T.Adj u v → Y u ∩ edgeBoundary Mn u v = Y v ∩ edgeBoundary Mn u v ∧
          (Y u ∩ edgeBoundary Mn u v).ncard ≤ 1) →
        Y = X) := by sorry

end RandDelMatroid.Indep
