-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_11
-- name    : TreeCorrMatch.ErrorFree.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:25:49.526261+00:00
-- url     : https://prove2.me/theorems/c022692a-6932-4243-b3c2-4376b41ba41a
-- title:
--   Lemma 11 — for every input pair, $e^{-1/16}L_d\le\hat L_d\le e^{1/16}L_d$ with probability at least $1-\xi$
-- statement:
--   Let $\lambda>0$, $s\in(0,1]$, $\xi\in(0,\tfrac12)$ and $d\ge0$, and fix trees $t,\tilde t$ of depth at most $d$. Let $\hat L_d(t,\tilde t)$ be the output of ApproxLR with parameters $\lambda,s,\xi,d$, where every call of the permanent approximator meets guarantee (15) and uses its own independent seed with law $\mu_0$. Then
--
--   $$\mathbb P\big(e^{-1/16}L_d(t,\tilde t)\le\hat L_d(t,\tilde t)\le e^{1/16}L_d(t,\tilde t)\big)\ \ge\ 1-\xi .$$
--
--   Combined with Lemma 10 this gives the constant-factor approximation of the likelihood ratio on which the test $\Psi$ of Theorem 3 rests.
--
--   Differences from the source:
--   - generalization: the FPRAS ApproxPer of [40] (Lemma 3, Remark 1) → every approximator App with seed law μ₀ that, for each entrywise nonnegative square matrix A and δ, η ∈ (0, 1/2), is measurable in the seed, nonnegative and meets guarantee (15); every call gets its own independent seed; reason: the paper uses only (15), nonnegativity and the fresh independent bits of Remark 1; the FPRAS of [40] is one such approximator, so the statement specializes to the paper's
--   - encoding: (t, t̃) ∈ Z_d × Z_d with children enumerated in an unspecified order → ordered trees of depth ≤ d, children in list order; reason: the statement holds for every ordered representative, hence for every enumeration
--   - encoding: fresh random bits for each ApproxPer execution → seeds ω : SeedIdx → Ω₀ with law Measure.infinitePi (fun _ => μ₀), one coordinate per call; reason: independent seeds, one per call, as in Remark 1
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 35, Lemma 11 (PDF p. 37)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_ApproxLR

open MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem lemma_11 {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀]
    (App : PermApprox Ω₀) (hApp : IsPermApprox μ₀ App) (lam s ξ : ℝ) (d : ℕ) (hlam : 0 < lam)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) (t t' : OTree)
    (ht : t.depth ≤ d) (ht' : t'.depth ≤ d) :
    1 - ξ ≤
      (Measure.infinitePi (fun _ : SeedIdx => μ₀)
        {ω | Real.exp (-(1 / 16)) * likelihoodRatio lam s d (cls t) (cls t') ≤
              approxLR App lam s ξ d t t' ω ∧
            approxLR App lam s ξ d t t' ω ≤
              Real.exp (1 / 16) * likelihoodRatio lam s d (cls t) (cls t')}).toReal := by sorry

end TreeCorrMatch.ErrorFree
