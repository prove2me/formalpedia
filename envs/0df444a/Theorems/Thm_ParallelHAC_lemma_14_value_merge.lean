-- Prove2me | Theorems.Thm_ParallelHAC_lemma_14_value_merge
-- name    : ParallelHAC.lemma_14_value_merge
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:17.679957+00:00
-- url     : https://prove2.me/theorems/ee6bd425-683a-4cf6-8676-bb373675508a
-- title:
--   Lemma 14 — a small merge shrinks value by $1/\sqrt2$
-- statement:
--   Let $d$ be a well-behaved linkage on a finite point set $P$, let $\tilde X\subseteq P$ be a nonempty cluster and $\tilde\delta>0$, and let $\mathrm{val}(A)=\exp_2(-d(\tilde X,A)/(4\tilde\delta))$. If $A,B\subseteq P$ are disjoint nonempty clusters with $d(A,B)\le2\tilde\delta$ and $|A|+|B|\le|\tilde X|$, then
--   $$\mathrm{val}(A\cup B)\le\frac1{\sqrt2}\bigl(\mathrm{val}(A)+\mathrm{val}(B)\bigr).$$
--
--   A merge of two nearby small clusters therefore lowers the total value; this is what makes the phase potential non-increasing (Lemma 15).
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - generalization: the phase objects X̃_j and δ̃_j → an arbitrary nonempty centre X̃ ⊆ P and scale δ̃ > 0; reason: the proof uses only average-reducibility at X̃; X̃ = X̃_j, δ̃ = δ̃_j is the paper's case
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: any disjoint A, B ⊆ ℝ^k → disjoint nonempty A, B ⊆ P; reason: the paper's linkages (and val_j) are undefined on ∅, and any A, B, X̃_j ⊆ ℝ^k lie in the point set P := A ∪ B ∪ X̃_j, over which the lemma is quantified
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 14, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_clusterValue

namespace ParallelHAC

/-- **Lemma 14** (p.19): a small merge shrinks value by `1/√2`. For a well-behaved linkage `d`,
a centre `X̃` and a scale `δ̃ > 0`, if `A, B` are disjoint, `d(A, B) ≤ 2δ̃` and
`|A| + |B| ≤ |X̃|`, then `val(A ∪ B) ≤ (1/√2)(val(A) + val(B))`, where
`val(·) = exp₂(−d(X̃, ·)/(4δ̃))`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 14, printed p.19 (PDF p.22).

**Formalization Note.** Stated for an arbitrary nonempty centre `X̃ ⊆ P` and scale `δ̃ > 0`; the
paper's `val_j` is the instance `X̃ = X̃_j`, `δ̃ = δ̃_j`. Clusters are nonempty subsets of `P`. -/
theorem lemma_14_value_merge {V : Type*} [DecidableEq V] (P : Finset V) (k : ℕ) (κ a cΔ b : ℝ)
    (d : Finset V → Finset V → ℝ) (hd : WellBehaved P k κ a cΔ b d)
    (Xt : Finset V) (δt : ℝ) (hXt : Xt.Nonempty) (hXtP : Xt ⊆ P) (hδt : 0 < δt)
    (A B : Finset V) (hA : A.Nonempty) (hAP : A ⊆ P) (hB : B.Nonempty) (hBP : B ⊆ P)
    (hAB : Disjoint A B) (hdAB : d A B ≤ 2 * δt) (hcard : A.card + B.card ≤ Xt.card) :
    clusterValue d Xt δt (A ∪ B) ≤
      1 / Real.sqrt 2 * (clusterValue d Xt δt A + clusterValue d Xt δt B) := by sorry

end ParallelHAC
