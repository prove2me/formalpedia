-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_theorem_3
-- name    : TreeCorrMatch.ErrorFree.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:42.88147+00:00
-- url     : https://prove2.me/theorems/9caa4365-e1ac-4e41-a89d-a8c1cf6f15c7
-- title:
--   Theorem 3 — the approximate test $\Psi=\mathbf 1\{\hat L_d>\theta^*\}$: nonnegative estimates, type-I error $\le n^{-(\log\log n)/2}+n^{-11}$, power $\ge1-7/\lambda-e^{1/8}n^{-(\log\log n)/2}-n^{-11}$
-- statement:
--   Let $s\in(\sqrt{C_{\mathrm{Otter}}},1]$ be a constant and $\lambda_n\to\infty$ with $\lambda_n\le(\log n)^K$ for some $K$. Set $d=\lceil(\log n)^{1/3}\rceil$, $\theta^*=e^{1/16}n^{(\log\log n)/2}$ and $\xi=n^{-11}$, and run ApproxLR with a permanent approximator meeting guarantee (15), independent seeds for its calls, independent of the trees. Then:
--
--   1. ApproxLR outputs a nonnegative estimate $\hat L_d(t,\tilde t)$ for every input pair of depth at most $d$ and the parameters $\lambda,s,\xi,d$;
--   2. the test $\Psi(t,\tilde t)=\mathbf 1\{\hat L_d(t,\tilde t)>\theta^*\}$ satisfies, for all sufficiently large $n$,
--
--   $$Q\big(\Psi([H_d],[\tilde H_d])=1\big)\le n^{-(\log\log n)/2}+n^{-11},$$
--
--   $$P\big(\Psi([H_d],[\tilde H_d])=1\big)\ge1-\frac7\lambda-e^{1/8}n^{-(\log\log n)/2}-n^{-11},$$
--
--   where the probabilities are over the tree pair and the algorithm's seeds.
--
--   This is the tree-correlation test with an explicit threshold used at every edge of the witness graphs of TBAlign.
--
--   **Formalization Note** Item 1 is stated for every $n\ge2$ with $\lambda_n>0$, where $\xi=n^{-11}\in(0,\tfrac12)$ and $\lambda>0$ are in ApproxLR's input domain. In item 2 the test is applied to $r(H_d),r(\tilde H_d)$ for the class-preserving map $r$.
--
--   Differences from the source:
--   - generalization: the FPRAS ApproxPer of [40] (Lemma 3, Remark 1) → every approximator App with seed law μ₀ that, for each entrywise nonnegative square matrix A and δ, η ∈ (0, 1/2), is measurable in the seed, nonnegative and meets guarantee (15); every call gets its own independent seed; reason: the paper uses only (15), nonnegativity and the fresh independent bits of Remark 1; the FPRAS of [40] is one such approximator, so the statement specializes to the paper's
--   - reading: ApproxLR receives the unlabeled pair ([T], [T̃]) and enumerates children in an unspecified order → ApproxLR acts on ordered trees; the test is applied to r(h), r(h̃) for an arbitrary fixed map r on ordered trees with [r(h)] = [h]; reason: the enumeration is left open by the paper; quantifying over every class-preserving r covers every rule (a canonical representative, or the order by vertex index)
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: 'for all sufficiently large n', with the constants independent of n → ∃ constants, then ∀ᶠ n in atTop; reason: standard reading
--   - encoding: nonnegativity 'for any input (t, t̃) ∈ Z_d × Z_d and parameters λ, s, ξ, d' → for every n ≥ 2 with λ_n > 0, every ordered input of depth ≤ d and every seed; reason: n ≥ 2 and λ_n > 0 put ξ = n^{-11} and λ in Algorithm 2's input domain (ξ ∈ (0, 1/2), λ > 0)
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 9, Theorem 3 (PDF p. 11); restated p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem theorem_3 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀]
    (App : PermApprox Ω₀) (hApp : IsPermApprox μ₀ App) (r : OTree → OTree)
    (hr : ∀ t, cls (r t) = cls t) :
    (∀ n : ℕ, 2 ≤ n → 0 < lam n → ∀ t t' : OTree, t.depth ≤ dParam n → t'.depth ≤ dParam n →
      ∀ ω : SeedIdx → Ω₀, 0 ≤ approxLR App (lam n) s (xiParam n) (dParam n) t t' ω) ∧
    ∀ᶠ n : ℕ in atTop,
      pairSeedProb (indepPairLaw (lam n) (dParam n)) (Measure.infinitePi fun _ : SeedIdx => μ₀)
          (fun h h' ω => thetaParam n < approxLR App (lam n) s (xiParam n) (dParam n) (r h) (r h') ω) ≤
        (n : ℝ) ^ (-Real.log (Real.log n) / 2) + (n : ℝ) ^ (-11 : ℝ) ∧
      1 - 7 / lam n - Real.exp (1 / 8) * (n : ℝ) ^ (-Real.log (Real.log n) / 2) - (n : ℝ) ^ (-11 : ℝ) ≤
        pairSeedProb (corrPairLaw (lam n) s (dParam n)) (Measure.infinitePi fun _ : SeedIdx => μ₀)
          (fun h h' ω => thetaParam n < approxLR App (lam n) s (xiParam n) (dParam n) (r h) (r h') ω) := by sorry

end TreeCorrMatch.ErrorFree
