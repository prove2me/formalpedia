-- Prove2me | Theorems.Thm_ParallelHAC_lemma_15_potential_nonincreasing
-- name    : ParallelHAC.lemma_15_potential_nonincreasing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:19.567832+00:00
-- url     : https://prove2.me/theorems/1ed42bf9-dba1-4971-b399-0b9d34c023dc
-- title:
--   Lemma 15 — the potential never increases within a phase
-- statement:
--   Let $d$ be a well-behaved linkage on $P$, fix a $c$-approximate HAC run ($c\ge1$), a point $x_0\in P$, and a phase $j$ with $\tilde\delta_j>0$. Then for every merge index $i\in I_j=[s_j,f_j]$,
--   $$\phi_j(\mathcal C_{i+1})\le\phi_j(\mathcal C_i),$$
--   where $\mathcal C_i$ is the clustering just before the $i$-th merge and $\phi_j$ is the potential of Definition 11.
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
--   - encoding: val_j(A) = exp2(−d(X̃_j, A)/(4·δ̃_j)) divides by δ̃_j → hypothesis 0 < δ̃_j; reason: excludes only the cases in which val_j is undefined
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 15, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_phaseEnd
import Definitions.Def_ParallelHAC_HACRun_phasePotential

namespace ParallelHAC

/-- **Lemma 15** (p.20): the potential never increases within a phase. For a well-behaved linkage,
a `c`-approximate HAC run, a point `x₀ ∈ P` and a phase `j`, `ϕ_j(C_i) ≥ ϕ_j(C_{i+1})` for every
merge `i ∈ I_j = [s_j, f_j]`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 15, printed p.20 (PDF p.23).

**Formalization Note.** `0 < δ̃_j` is the nondegeneracy under which `val_j` (a division by `δ̃_j`)
is defined; `cΔ ≥ 1` as on p.19. -/
theorem lemma_15_potential_nonincreasing {V : Type*} [DecidableEq V] (P : Finset V) (k : ℕ)
    (κ a cΔ b c : ℝ) (d : Finset V → Finset V → ℝ) (hcΔ : 1 ≤ cΔ) (hc : 1 ≤ c)
    (hd : WellBehaved P k κ a cΔ b d) (R : HACRun P d c) (x₀ : V) (hx₀ : x₀ ∈ P)
    (j : ℕ) (hj : R.IsPhase x₀ cΔ j) (hδ : 0 < R.maxMergeValue (R.phaseStart x₀ cΔ j)) (i : ℕ)
    (hi₁ : R.phaseStart x₀ cΔ j ≤ i) (hi₂ : i ≤ R.phaseEnd x₀ cΔ j) :
    R.phasePotential x₀ cΔ j (R.C (i + 1)) ≤ R.phasePotential x₀ cΔ j (R.C i) := by sorry

end ParallelHAC
