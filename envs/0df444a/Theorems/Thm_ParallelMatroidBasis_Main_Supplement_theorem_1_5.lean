-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_theorem_1_5
-- name    : ParallelMatroidBasis.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:11.075241+00:00
-- url     : https://prove2.me/theorems/3769f032-f4c0-40ac-b2b9-5672e6a5a755
-- title:
--   Theorem 1.5 — a $(1/2-\epsilon)$-approximation for monotone submodular maximization under a matroid constraint in $\tilde O(n^{1/3}/\epsilon^3)$ rounds
-- statement:
--   There is an exponent $k\in\mathbb N$ such that for every $c>0$ there are constants $C>0$ and $d\in\mathbb N$ such that for every $\varepsilon>0$ there is one randomized parallel algorithm $A_\varepsilon$ — one procedure for every ground-set size $n$, seeing a matroid $M=(E,\mathcal I)$ on $E=[n]$ only through independence queries and a set function $f$ only through value queries — such that for all $n$, every such matroid $M$ and every monotone submodular $f:2^E\to\mathbb R_{\ge0}$ ($A\subseteq B\Rightarrow f(A)\le f(B)$; $f(A)+f(B)\ge f(A\cup B)+f(A\cap B)$):
--
--   1. every run uses at most $C\,\big(1+n^{1/3}(\log_2(n+2))^k/\varepsilon^3\big)$ adaptive rounds;
--   2. every run makes at most $(n+1)^d$ independence queries to $M$ and at most $(n+1)^d$ queries to $f$ in total;
--   3. if $n\ge1$, with probability at least $1-n^{-c}$ the output $S$ satisfies
--   $$S\in\mathcal I\qquad\text{and}\qquad f(S)\ \ge\ \Big(\tfrac12-\varepsilon\Big)\max_{T\in\mathcal I}f(T).$$
--
--   The constants $C$, $d$ and the exponent $k$ do not depend on $\varepsilon$. This improves the $\tilde O(n^{3/7}/\varepsilon^3)$ rounds of [KPS26] for the independence-query model; no normalization $f(\emptyset)=0$ is assumed.
--
--   **Formalization Note** The query model is `MultiOracle`'s `SubmodAlgorithm`. Monotonicity and submodularity reuse the published `SubsamplingSM.Offline.IsMonotoneSetFn` and `NonmonotoneSubmod.Shared.Submodular`; nonnegativity is a separate hypothesis. The maximum is encoded as "$f(S)\ge(1/2-\varepsilon)f(T)$ for every independent $T$". $\tilde O$ is read as a fixed power of $\log_2(n+2)$, "with high probability" as failure at most $n^{-c}$ for every $c>0$.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many queries → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n) ⊕ Finset (Fin n)) (Bool ⊕ ℝ) (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: a matroid M on n elements → a Matroid (Fin n) with ground set univ; reason: the algorithm knows the n labels of the ground set, as in the source's oracle model (same convention as the base mission)
--   - encoding: a monotone submodular function f : 2^E → R≥0, accessed by queries → f : Finset (Fin n) → ℝ with IsMonotoneSetFn f, Submodular f (lattice inequality) and 0 ≤ f S for all S; value queries return f(T) exactly; reason: the source's three conditions, with no normalization f(∅) = 0, as in the source
--   - reading: for any ε > 0, an Õ(n^{1/3}/ε^3) round algorithm → ∃ k : ℕ, then for each c ∃ C > 0 and d, then for each ε > 0 an algorithm with at most C(1 + n^{1/3}(log₂(n+2))^k/ε³) rounds on every run; reason: Õ hides a polylogarithmic factor in n; C, d, k uniform in ε is the stronger reading (the O(·) keeps 1/ε³ explicit); log₂(n+2) ≥ 1 keeps the factor defined at n ≤ 1
--   - reading: polynomially many independence queries to M and polynomially many queries to f → at most (n+1)^d independence queries and at most (n+1)^d value queries over the whole run, d independent of ε; reason: the source states query totals, not per-round counts; a total bound is the stronger reading and implies a per-round bound
--   - reading: with high probability → for every c > 0 (with constants and algorithm depending on c), for n ≥ 1 the success probability is at least 1 − n^{−c}; reason: the base mission's reading of the paper's 'with high probability'; the proofs amplify to inverse-polynomial failure for an arbitrary exponent (PDF pp.37, 41); this is the stronger reading
--   - encoding: S ∈ I with f(S) ≥ (1/2 − ε) max_{T∈I} f(T) → M.Indep S and (1/2 − ε) f(T) ≤ f(S) for every independent T; reason: the maximum over the finite nonempty family I is attained, so the two conditions coincide
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 1.5, p.3 (PDF p.5); proof via Lemma B.2 and Lemma B.3 ([BRS19b]), p.35 (PDF p.37)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_MultiOracle

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

/-- Theorem 1.5, PDF p.5 (printed p.3), with `Õ(·)` read as a polylogarithmic factor
`(log₂ (n+2))^k` and "with high probability" as failure probability at most `n^{−c}` for every
fixed `c > 0`. There is `k` such that for every `c > 0` there are `C > 0` and `d` such that for
every `ε > 0` there is one parallel algorithm `A` (a protocol for every `n`, seeing `M` only
through independence queries and `f` only through value queries) such that for all `n`, every
matroid `M` on `Fin n` and every monotone submodular `f : 2^{Fin n} → ℝ≥0`: every run uses at most
`C (1 + n^{1/3} (log₂ (n+2))^k / ε³)` rounds, at most `(n+1)^d` independence queries and at most
`(n+1)^d` value queries in total, and for `n ≥ 1`, with probability at least `1 − n^{−c}`, the
output `S` is independent and `f(S) ≥ (1/2 − ε) max_{T ∈ I} f(T)`. -/
theorem theorem_1_5 :
    ∃ k : ℕ, ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ ε : ℝ, 0 < ε →
        ∃ A : SubmodAlgorithm,
          ∀ (n : ℕ) (M : Matroid (Fin n)) (f : Finset (Fin n) → ℝ), M.E = Set.univ →
            SubsamplingSM.Offline.IsMonotoneSetFn f → NonmonotoneSubmod.Shared.Submodular f →
            (∀ S, 0 ≤ f S) →
            RunRoundsAtMost (A n) (submodOracle M f)
              (C * (1 + (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.logb 2 ((n : ℝ) + 2)) ^ k / ε ^ 3)) ∧
            RunTotalQueriesAtMost (A n) (submodOracle M f) IsIndepQuery ((n + 1) ^ d) ∧
            RunTotalQueriesAtMost (A n) (submodOracle M f) IsValueQuery ((n + 1) ^ d) ∧
            (1 ≤ n → ENNReal.ofReal (1 - (n : ℝ) ^ (-c)) ≤ submodSuccessProb A n M f ε)
      := by sorry

end ParallelMatroidBasis.Main.Supplement
