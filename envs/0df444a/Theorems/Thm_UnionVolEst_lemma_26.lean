-- Prove2me | Theorems.Thm_UnionVolEst_lemma_26
-- name    : UnionVolEst.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:03:45.978605+00:00
-- url     : https://prove2.me/theorems/8ef31d0a-389f-445e-8e91-6ba74ee4b033
-- title:
--   Lemma 26 — Poissonization: counts of a Poisson number of samples in a partition are independent Poisson
-- statement:
--   Let $D$ be a probability distribution on a measurable space $S$ and $S=S_1\sqcup\dots\sqcup S_L$ a partition into disjoint measurable sets. Let $N\sim\mathrm{Pois}(\lambda)$, $\lambda\ge0$, and, independently of $N$, let $W_0,W_1,\dots$ be independent samples from $D$. For each $j$ let $N_j=\#\{k<N: W_k\in S_j\}$. Then $N_1,\dots,N_L$ are mutually independent and
--   $$
--   N_j\sim\mathrm{Pois}\big(\lambda D(S_j)\big)\qquad(j=1,\dots,L).
--   $$
--   This splitting property turns Poisson sampling on a continuous space into independent Poisson counts on disjoint regions, which is how the analysis works directly with volumes.
--
--   Differences from the source:
--   - encoding: N ∼ Pois(λ) and, conditional on N, N independent samples from D → an i.i.d. sequence W₀, W₁, … of law D independent of N, of which the first N are used; reason: the standard realization of "conditional on N, draw N independent samples"; same joint law
--   - encoding: probability space (S, ν) → measurable space S (ν dropped); reason: ν plays no role in the statement
--   - generalization: N ∼ Pois(λ) (λ unrestricted on the page; Lemma 25 takes λ > 0) → λ ∈ ℝ≥0, including λ = 0; reason: at λ = 0 the counts are all 0; every λ > 0 is covered
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Lemma 26, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_UnionVolEst_countIn

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Lemma 26 (Poissonization) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.41, PDF p.43: let `D` be a probability distribution on
`S` and `S = S₁ ⊔ ⋯ ⊔ S_L` a partition into disjoint measurable sets. If `N ∼ Pois(λ)` and,
conditional on `N`, `N` independent samples are drawn from `D`, then the numbers `N_j` of samples
in `S_j` are mutually independent and `N_j ∼ Pois(λ D(S_j))`.

**Formalization Note** "Conditional on `N`, draw `N` independent samples" is realized by an
i.i.d. sequence `W₀, W₁, …` of law `D`, independent of `N`, of which the first `N` are used. The
reference measure `ν` of the page plays no role and is dropped. `λ ≥ 0`. -/
theorem lemma_26 {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure S) [IsProbabilityMeasure D]
    {L : ℕ} (Sp : Fin L → Set S) (hSp : ∀ j, MeasurableSet (Sp j))
    (hdisj : Pairwise (Function.onFun Disjoint Sp)) (hcover : ⋃ j, Sp j = Set.univ)
    (lam : ℝ≥0) (N : Ω → ℕ) (W : ℕ → Ω → S)
    (hN : HasLaw N (poissonMeasure lam) P) (hW : ∀ k, HasLaw (W k) D P)
    (hWind : iIndepFun W P) (hNW : IndepFun N (fun ω k => W k ω) P) :
    iIndepFun (fun j ω => countIn ((List.range (N ω)).map (fun k => W k ω)) (Sp j)) P ∧
      ∀ j, HasLaw (fun ω => countIn ((List.range (N ω)).map (fun k => W k ω)) (Sp j))
        (poissonMeasure (lam * (D (Sp j)).toNNReal)) P := by sorry

end UnionVolEst
