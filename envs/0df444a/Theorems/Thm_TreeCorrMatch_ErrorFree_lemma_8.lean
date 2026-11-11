-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_8
-- name    : TreeCorrMatch.ErrorFree.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:27:41.214141+00:00
-- url     : https://prove2.me/theorems/00f33ae0-59b2-4ae1-8ebb-69bd66a061ee
-- title:
--   Lemma 8 — a true pair $(u,\tilde u)$ passes the 5-dangling-tree test except with probability $O(n^{-1/2}+e^{-\lambda s/2})$
-- statement:
--   Under the assumptions of Theorem 1, for every node $u$ the event $A_{3,u}$, that $\mathrm{GreedyMatching}(W^\infty(u,\tilde u),\theta^*,5)=1$ for TBAlign without degree cutoff, satisfies
--
--   $$\mathbb P(A_{3,u}^c)=O\big(n^{-1/2}+\exp(-\lambda s/2)\big),$$
--
--   with one constant, independent of $n$ and $u$, for all large $n$. Here $A_{3,u}$ requires the output $1$ for **every** order in which GreedyMatching examines the edges.
--
--   Through Markov's inequality this shows that all but $o(n)$ nodes are matched to their counterparts.
--
--   Differences from the source:
--   - generalization: the FPRAS ApproxPer of [40] (Lemma 3, Remark 1) → every approximator App with seed law μ₀ that, for each entrywise nonnegative square matrix A and δ, η ∈ (0, 1/2), is measurable in the seed, nonnegative and meets guarantee (15); every call gets its own independent seed; reason: the paper uses only (15), nonnegativity and the fresh independent bits of Remark 1; the FPRAS of [40] is one such approximator, so the statement specializes to the paper's
--   - reading: ApproxLR receives the unlabeled pair ([T], [T̃]) and enumerates children in an unspecified order → ApproxLR acts on ordered trees; the test is applied to r(h), r(h̃) for an arbitrary fixed map r on ordered trees with [r(h)] = [h]; reason: the enumeration is left open by the paper; quantifying over every class-preserving r covers every rule (a canonical representative, or the order by vertex index)
--   - reading: A_3,u = {GreedyMatching(W^∞(u, ũ), θ*, 5) = 1} with an arbitrary edge order → the output is 1 for every admissible order; reason: the order is arbitrary; the proof's nine-pair argument holds for every order
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: O(n^{-1/2} + exp(−λs/2)) → ∃ C, for all large n and every u: probability ≤ C (n^{-1/2} + exp(−λ_n s/2)); reason: the O-constant is independent of n and of u
--   - encoding: CER(n, λ, s) with parent edge probability λ/(ns), λ ∈ (0, ns] → parent edge probability clamped to [0, 1]; reason: the clamp changes only the finitely many n with λ_n > ns and no limit
--   - encoding: Otter's constant C_Otter ≈ 0.338 (cited from [14], not defined in the paper) → otterConst = sup{x ≥ 0 : ∑_m r_m x^m converges}, r_m the number of rooted unlabeled trees with m nodes; reason: the radius of convergence of the generating function of rooted unlabeled trees is Otter's constant 1/α ≈ 0.3383
--   - encoding: node set [n] → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 20, Lemma 8 (PDF p. 22)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem lemma_8 (s : ℝ) (hs : Real.sqrt otterConst < s) (hs1 : s ≤ 1) (lam : ℕ → ℝ)
    (hlam : Tendsto lam atTop atTop) (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀]
    (App : PermApprox Ω₀) (hApp : IsPermApprox μ₀ App) (r : OTree → OTree)
    (hr : ∀ t, cls (r t) = cls t) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ u : Fin n,
      cerSeedProb n (lam n) s (tbSeedLaw μ₀ n) (fun x ω => ¬ EventA3 App r (lam n) s x ω u) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) + Real.exp (-(lam n * s / 2))) := by sorry

end TreeCorrMatch.ErrorFree
