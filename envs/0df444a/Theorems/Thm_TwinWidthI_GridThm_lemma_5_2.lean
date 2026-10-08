-- Prove2me | Theorems.Thm_TwinWidthI_GridThm_lemma_5_2
-- name    : TwinWidthI.GridThm.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:18.59182+00:00
-- url     : https://prove2.me/theorems/b5b1e653-72ab-4ef8-8f29-d7df994574aa
-- title:
--   Lemma 5.2 — an r-refining sequence of partitions with error value t gives twin-width at most rt
-- statement:
--   Let $M$ be an $n\times m$ matrix over a finite alphabet and let $(\mathcal R^0,\mathcal C^0),\dots,(\mathcal R^N,\mathcal C^N)$ be a sequence of partitions of $M$ such that
--
--   1. $(\mathcal R^0,\mathcal C^0)$ is the finest partition;
--   2. $(\mathcal R^N,\mathcal C^N)$ is the coarsest partition;
--   3. for every $i<N$, $\mathcal R^i$ $r$-refines $\mathcal R^{i+1}$ and $\mathcal C^i$ $r$-refines $\mathcal C^{i+1}$ (every part of the former lies in a part of the latter, and every part of the latter contains at most $r$ parts of the former);
--   4. every $(\mathcal R^i,\mathcal C^i)$ has error value at most $t$.
--
--   Then $$\operatorname{tww}(M)\le r\,t.$$
--
--   The sequence need not perform one contraction at a time; the lemma converts such a coarse sequence into a genuine contraction sequence. It is the final step of the proof of Theorem 5.4.
--
--   **Formalization Note** The conclusion is `MatTwinWidthLE M (r * t)` in the partition form of twin-width. The sequence is indexed by `Fin (N + 1)`.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:18, Lemma 5.2

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

namespace TwinWidthI.GridThm

/-- Lemma 5.2, p. 3:18: a sequence of partition pairs from the finest to the coarsest partition in
which each pair `r`-refines the next and every pair has error value at most `t` shows that `M`
has twin-width at most `r t`. -/
theorem lemma_5_2 {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (r t N : ℕ)
    (R : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin n)))
    (C : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin m)))
    (hR0 : R 0 = ⊥) (hC0 : C 0 = ⊥)
    (hRN : (R (Fin.last N)).parts.card ≤ 1) (hCN : (C (Fin.last N)).parts.card ≤ 1)
    (hrefR : ∀ i : Fin N, KRefines r (R i.castSucc) (R i.succ))
    (hrefC : ∀ i : Fin N, KRefines r (C i.castSucc) (C i.succ))
    (herr : ∀ i, ErrorLE M (R i) (C i) t) :
    MatTwinWidthLE M (r * t) := by sorry

end TwinWidthI.GridThm
