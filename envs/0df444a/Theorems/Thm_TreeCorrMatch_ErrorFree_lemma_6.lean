-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_6
-- name    : TreeCorrMatch.ErrorFree.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:27:59.602207+00:00
-- url     : https://prove2.me/theorems/85d813f2-3b3c-4bb4-93fa-119cb7929005
-- title:
--   Lemma 6 — $\mathbb P(A_1^c)=\tilde O(n^{-1/3})$
-- statement:
--   Under the assumptions of Theorem 1 (a constant $s\in(\sqrt{C_{\mathrm{Otter}}},1]$, $\lambda_n\to\infty$ with $\lambda_n\le(\log n)^K$, a permanent approximator meeting guarantee (15) with fresh independent seeds, class-preserving representatives), the event $A_1$ (no pair of node-disjoint local trees without degree cutoff passes the test $\Psi$) satisfies
--
--   $$\mathbb P(A_1^c)=\tilde O(n^{-1/3}),$$
--
--   that is, there are constants $C$ and $K'$ with $\mathbb P(A_1^c)\le C(\log n)^{K'}n^{-1/3}$ for all large $n$, the probability being over the graphs, $\pi$ and the seeds.
--
--   Differences from the source:
--   - generalization: the FPRAS ApproxPer of [40] (Lemma 3, Remark 1) → every approximator App with seed law μ₀ that, for each entrywise nonnegative square matrix A and δ, η ∈ (0, 1/2), is measurable in the seed, nonnegative and meets guarantee (15); every call gets its own independent seed; reason: the paper uses only (15), nonnegativity and the fresh independent bits of Remark 1; the FPRAS of [40] is one such approximator, so the statement specializes to the paper's
--   - reading: ApproxLR receives the unlabeled pair ([T], [T̃]) and enumerates children in an unspecified order → ApproxLR acts on ordered trees; the test is applied to r(h), r(h̃) for an arbitrary fixed map r on ordered trees with [r(h)] = [h]; reason: the enumeration is left open by the paper; quantifying over every class-preserving r covers every rule (a canonical representative, or the order by vertex index)
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: Õ(n^{-1/3}) → ∃ C, K, for all large n: probability ≤ C (log n)^K n^{-1/3}; reason: Õ suppresses a polylogarithmic factor
--   - encoding: CER(n, λ, s) with parent edge probability λ/(ns), λ ∈ (0, ns] → parent edge probability clamped to [0, 1]; reason: the clamp changes only the finitely many n with λ_n > ns and no limit
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 18, Lemma 6 (PDF p. 20)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem lemma_6 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀]
    (App : PermApprox Ω₀) (hApp : IsPermApprox μ₀ App) (r : OTree → OTree)
    (hr : ∀ t, cls (r t) = cls t) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      cerSeedProb n (lam n) s (tbSeedLaw μ₀ n) (fun x ω => ¬ EventA1 App r (lam n) s x ω) ≤
        C * Real.log n ^ K * (n : ℝ) ^ (-(1 : ℝ) / 3) := by sorry

end TreeCorrMatch.ErrorFree
