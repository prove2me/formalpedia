-- Prove2me | Theorems.Thm_StableCount_lemma_3_6
-- name    : StableCount.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:21.778681+00:00
-- url     : https://prove2.me/theorems/6a24dcee-e37f-483b-acc1-158ac806ce1d
-- title:
--   Lemma 3.6 — deleting a downset and an upset leaves a rotation poset on the same people
-- statement:
--   Let $Q$ be the rotation poset of a normalized instance $I$, $D$ a downset and $U$ an upset of $Q$ with $D\cap U=\emptyset$, and $P=Q\setminus(D\cup U)$. There is a normalized instance $I_P$ on the same people whose rotation poset is the induced poset on $P$, and each person's rotation chain consists of their retained rotations. The map
--   $$
--   K\longmapsto D\cup K
--   $$
--   is a bijection from the downsets of $P$ to the downsets of $Q$ that contain $D$ and avoid $U$. Corresponding downsets give the same matching in $I_P$ and $I$.
--
--   This shows that the induction of the paper stays inside the family of rotation posets of normalized instances.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: "rotation poset is the induced poset on P", "chain consists of the retained rotations" → IsRestriction: an order isomorphism e from P to the rotations of Q_P under which each actual person's participation is unchanged; reason: people rather than labels, since a woman's label is defined anew (p.14); a person's rotations are pairwise comparable, so e preserves their chain order
--   - encoding: "Corresponding downsets give the same matching" → for a downset K' of Q_P: matchingOf K' = matchingOf (D ∪ e⁻¹(K')); reason: e carries the downsets of P onto those of Q_P; matchingOf applies the rotations in increasing order, and any linear extension gives the same matching by Lemma 3.3
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 3.6, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_StableCount_Member

namespace StableCount

/-- Lemma 3.6 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 3.6, p.12). Let `D` be a downset and `U` an upset of `Q` with `D ∩ U = ∅`, and
put `P = Q \ (D ∪ U)`. There is a normalized instance `I_P` on the same people whose rotation poset is the
induced poset on `P`, and each person's rotation chain consists of their retained rotations. The map
`K ↦ D ∪ K` is a bijection from the downsets of `P` to the downsets of `Q` that contain `D` and avoid `U`.
Corresponding downsets give the same matching in `I_P` and `I`. -/
theorem lemma_3_6 {n : ℕ} (Q : Member n) (D U : Finset (Fin Q.R))
    (hD : Q.IsDownsetIn Finset.univ D) (hU : Q.IsUpset U) (hDU : Disjoint D U) :
    ∃ (QP : Member n) (e : {i // i ∈ Finset.univ \ (D ∪ U)} ≃ Fin QP.R),
      Q.IsRestriction (Finset.univ \ (D ∪ U)) QP e ∧
      Set.BijOn (fun K => D ∪ K) {K | Q.IsDownsetIn (Finset.univ \ (D ∪ U)) K}
        {K | Q.IsDownsetIn Finset.univ K ∧ D ⊆ K ∧ Disjoint K U} ∧
      ∀ K' : Finset (Fin QP.R), QP.IsDownsetIn Finset.univ K' →
        QP.matchingOf K' = Q.matchingOf (D ∪ K'.image fun j => (e.symm j : Fin Q.R)) := by sorry

end StableCount
