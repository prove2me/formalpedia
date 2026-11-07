-- Prove2me | Theorems.Thm_ParallelHAC_lemma_16_potential_start
-- name    : ParallelHAC.lemma_16_potential_start
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:37.798881+00:00
-- url     : https://prove2.me/theorems/d8e176ea-917a-4d9a-a259-5cb7a26f696f
-- title:
--   Lemma 16 — the potential starts at $\tilde O((k\cdot c)^{O(k)})$
-- statement:
--   For all packing constants $\kappa,a>0$ there is a constant $C>0$ such that the following holds. Let $d$ be a well-behaved linkage on a finite point set $P$ with $n=|P|$, dimension parameter $k\ge1$ and triangle constant $c_\Delta\ge1$; fix a $c$-approximate HAC run ($c\ge1$), a point $x_0\in P$ and a phase $j$ with $\tilde\delta_j>0$. Then
--   $$\phi_j(\mathcal C_{s_j})\le C\,(\log_2 n+1)^{C}\,(k\,c)^{C k}.$$
--
--   The potential at the start of a phase is controlled by packing: the clusters just before the largest merge so far are $\tilde\delta_j/c$-separated.
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: Õ((k · c)^{O(k)}) → C(log₂ n + 1)^C (k c)^{Ck} for a constant C chosen before the point type, the instance and the run; reason: pins the asymptotic notation with constants depending only on the fixed structural constants, as in the paper's proof
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
--   - encoding: val_j(A) = exp2(−d(X̃_j, A)/(4·δ̃_j)) divides by δ̃_j → hypothesis 0 < δ̃_j; reason: excludes only the cases in which val_j is undefined
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 16, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_rate
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_phaseEnd
import Definitions.Def_ParallelHAC_HACRun_phasePotential

namespace ParallelHAC

universe u

/-- **Lemma 16** (p.21): the potential starts at `Õ((k·c)^{O(k)})`. There is a constant `C`,
depending only on the packing constants `κ, a`, such that for every well-behaved linkage on a point
set `P` with dimension parameter `k ≥ 1`, every `c`-approximate HAC run (`c ≥ 1`), every
`x₀ ∈ P` and every phase `j`, `ϕ_j(C_{s_j}) ≤ C (log₂ n + 1)^C (k c)^{C k}` with `n = |P|`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 16, printed p.21 (PDF p.24).

**Formalization Note.** `Õ((k·c)^{O(k)})` is `rate C n k c`; the constant `C` is chosen before the
point type, the instance and the run. `0 < δ̃_j` is the nondegeneracy under which `val_j` (a division by
`δ̃_j`) is defined. -/
theorem lemma_16_potential_start :
    ∀ κ a : ℝ, 0 < κ → 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (cΔ b c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ k → 1 ≤ cΔ → 1 ≤ c → WellBehaved P k κ a cΔ b d →
    ∀ (R : HACRun P d c) (x₀ : V), x₀ ∈ P →
    ∀ j : ℕ, R.IsPhase x₀ cΔ j → 0 < R.maxMergeValue (R.phaseStart x₀ cΔ j) →
      R.phasePotential x₀ cΔ j (R.C (R.phaseStart x₀ cΔ j)) ≤ rate C P.card k c := by sorry

end ParallelHAC
