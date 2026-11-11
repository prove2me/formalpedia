-- Prove2me | Theorems.Thm_STCSublinear1377_Main_lemma_3_1
-- name    : STCSublinear1377.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:56.887526+00:00
-- url     : https://prove2.me/theorems/f26bfdf3-d5b2-4271-84d5-9fe585c058f7
-- title:
--   Lemma 3.1 — Minimum cuts survive isolating-set contractions
-- statement:
--   Let $F$ be a connected positive-weight graph and $H'\subseteq H\subseteq V_F$. Let the sets $S_h$, for $h\in H'$, be pairwise disjoint, meet $H$ only in $h$, and attain the minimum cut separating $h$ from the other hubs. Contract them, retaining the names $h$, and put $R=(V_F\setminus\bigcup_{h\in H'}S_h)\cup H'$. For every disjoint $A,B\subseteq H\setminus H'$ and, more generally, for every disjoint $A,B\subseteq R$,
--
--   $$\operatorname{mincut}_{F/\mathcal S}(A,B)=\operatorname{mincut}_F(A,B).$$
--
--   The retained-terminal clause permits repeated contractions while preserving the separating cut values required by the laminar construction. Connectedness of the individual isolating sets is not an extra premise of this lemma.
--
--   Differences from the source:
--   - generalization: the connected simple unweighted original graph and its positive-integer weighted quotients → any connected positive-real-weight graph; reason: the cut uncrossing argument uses nonnegative cut weights and no integrality, and includes every source graph
--   - encoding: finite vertex sets and contraction labels → active subsets of Fin n with explicit named bags; reason: this enumerates the same vertices, retains every uncontracted name and adds no condition on a selected cut
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 3.1 and (3.1), PDF/printed p.7; proof continues p.8

import Definitions.Def_STCSublinear1377_Main_Quotient
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Includes the retained-terminal extension, not only terminals in H \ H'. -/
theorem lemma_3_1 :
    ∀ n : ℕ, ∀ f : WeightedGraph n, f.positive → f.connected →
      ∀ h hs : Finset (Fin n), ∀ sets : Fin n → Finset (Fin n),
        isolatingSets f h hs sets →
        (∀ a b : Finset (Fin n), a ⊆ h \ hs → b ⊆ h \ hs → Disjoint a b →
          (contract f hs sets).mincut a b = f.mincut a b) ∧
        (∀ a b : Finset (Fin n), a ⊆ contractionNames f hs sets →
          b ⊆ contractionNames f hs sets → Disjoint a b →
          (contract f hs sets).mincut a b = f.mincut a b) := by sorry

end STCSublinear1377.Main
