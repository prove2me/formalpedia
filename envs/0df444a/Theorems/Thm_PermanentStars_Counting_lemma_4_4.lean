-- Prove2me | Theorems.Thm_PermanentStars_Counting_lemma_4_4
-- name    : PermanentStars.Counting.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:13.369845+00:00
-- url     : https://prove2.me/theorems/70139211-403b-428c-92ca-4b455951929c
-- title:
--   Lemma 4.4 — Polynomial size signed star-formation gadget
-- statement:
--   Fix valid cutoff data $R,\alpha$ and $r\in R$. There is a constant $C>0$, independent of $n$ and the nursery $d$, such that whenever the standing coverage assumption holds and $\sum_jd_j\le n$, the concrete serial star-formation graph is an ABP with labels $\pm1$, output $C_r(d)$, and
--   $$|V|+|E|\le C(n+1)^{|R|+4}.$$
--   The output equals the defining partition sum for every family of disjoint clusters of the prescribed sizes, so the cluster-label choice does not change it. Parallel Grow transitions are counted separately. This supplies the deferred-star component of each cutoff graph.
--
--   Differences from the source:
--   - encoding: the constructed object is an ABP → acyclicity and the source and sink conditions are explicit conclusions; reason: the semantic graph type itself contains no correctness or acyclicity certificate
--   - encoding: a star-formation gadget of size O(n^{|R|+4}) → the displayed serial construction with an all-n bound C(n+1)^{|R|+4} and explicit equality for arbitrary disjoint clusters; reason: finite initial n are absorbed by C; the construction in the proof realizes the existential gadget and establishes that the defining cluster choice is immaterial
--   - encoding: integer cluster sizes, open-star sizes and counters at selected cutoffs s at least r → finite coordinate carriers bounded by n, with additional zero counters at selected cutoffs below r; reason: each source-reachable count is at most n and the additional counters stay zero; the closed marker remains k=0 and no path contribution is removed
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Lemma 4.4, PDF/printed p.9

import Definitions.Def_PermanentStars_Counting_Gadgets

namespace PermanentStars.Counting

/-- Lemma 4.4, p.9. Constants precede n and the nursery; n+1 absorbs n=0 into the O bound. -/
theorem lemma_4_4 (P : Cutoffs) (hP : P.Valid) (r : ℕ) (hr : r ∈ P.R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (coverage : Covers P n) (d : Nursery n),
      nurseryMass d ≤ n →
      (formationABP P r d).IsABP ∧
      (∀ e ∈ (formationABP P r d).edges, e.2.2 = .one ∨ e.2.2 = .negOne) ∧
      (formationABP P r d).output (Label.eval (fun _ _ => (0 : ℤ))) = formationCoefficient P r d ∧
      (∀ U : Fin n → Finset (Fin n),
        (∀ j, (U j).card = (d j).val) → (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
        (formationABP P r d).output (Label.eval (fun _ _ => (0 : ℤ))) = formationCoefficientOn P r U) ∧
      ((formationABP P r d).size : ℝ) ≤ C * (n + 1 : ℝ) ^ (P.R.card + 4) := by sorry

end PermanentStars.Counting
