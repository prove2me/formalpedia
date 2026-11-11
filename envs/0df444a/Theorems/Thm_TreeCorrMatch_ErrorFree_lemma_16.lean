-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_16
-- name    : TreeCorrMatch.ErrorFree.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:28:05.616811+00:00
-- url     : https://prove2.me/theorems/276b1bec-c881-4fe0-8d45-7224630f00b8
-- title:
--   Lemma 16 — the degree cutoff affects few nodes: $|B|+|\tilde B|\le2ne^{-(\log n)^{2/5}}$ with probability $\ge1-2e^{-(\log n)^{2/5}}$
-- statement:
--   Let $G,\tilde G$ be two Erdős–Rényi graphs $\mathrm{ER}(n,\lambda/n)$ with $\lambda_n\to\infty$ and $\lambda_n\le(\log n)^K$ for some $K$, and let $d$ and $\tau$ be as in (1). For the sets $B$ and $\tilde B$ of nodes whose $(d+1)$-hop neighbourhood contains a node of degree larger than $\tau$,
--
--   $$|B|+|\tilde B|\le 2n\exp\big(-(\log n)^{2/5}\big)$$
--
--   with probability at least $1-2\exp(-(\log n)^{2/5})$, for all sufficiently large $n$, whatever the joint law of $(G,\tilde G)$.
--
--   The cutoff therefore changes only $o(n)$ of the witness graphs $W(u,\tilde u)$, which is how the analysis without cutoff carries over to TBAlign.
--
--   Differences from the source:
--   - encoding: λ = ω(1), λ = (log n)^{O(1)} → λ : ℕ → ℝ with λ_n → ∞ and ∃ K ∈ ℕ, λ_n ≤ (log n)^K for all large n; reason: standard reading of the Landau symbols
--   - encoding: 'for all sufficiently large n', with the constants independent of n → ∃ constants, then ∀ᶠ n in atTop; reason: standard reading
--   - reading: two Erdős–Rényi graphs G, G̃ ∼ ER(n, λ/n), joint law unspecified → every joint law μ whose two marginals are ER(n, λ_n/n); reason: the statement fixes only the marginals; CER is one such joint law
--   - encoding: ER(n, λ/n) → the published Erdős–Rényi law RGGDetect.erLaw n (λ_n / n); reason: same object
--   - reading: τ as reprinted in (114), max{√(log n), λ(1 + 1/log log n)} without a ceiling → τ = ⌈max{√(log n), λ(1 + 1/log log n)}⌉ of (1) (tauParam); reason: (114) is introduced as "recall the parameters d and τ defined in (1)" and the lemma says "Choose d and τ as in (1)"; the dropped ceiling is a reprint typo
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), pp. 50–51, Lemma 16 (PDF pp. 52–53)

import Mathlib
import Definitions.Def_RGGDetect_erLaw
import Definitions.Def_TreeCorrMatch_ErrorFree_AnalysisEvents

open Filter Topology MeasureTheory

namespace TreeCorrMatch.ErrorFree

theorem lemma_16 (lam : ℕ → ℝ) (hlam : Tendsto lam atTop atTop)
    (hpoly : ∃ K : ℕ, ∀ᶠ n in atTop, lam n ≤ Real.log n ^ K) :
    ∀ᶠ n : ℕ in atTop, ∀ μ : Measure (SimpleGraph (Fin n) × SimpleGraph (Fin n)),
      μ.map Prod.fst = RGGDetect.erLaw n (lam n / n) →
      μ.map Prod.snd = RGGDetect.erLaw n (lam n / n) →
      1 - 2 * Real.exp (-(Real.log n ^ ((2 : ℝ) / 5))) ≤
        (μ {p | ((cutoffSet p.1 (dParam n) (tauParam n (lam n))).ncard : ℝ) +
                  (cutoffSet p.2 (dParam n) (tauParam n (lam n))).ncard ≤
                2 * n * Real.exp (-(Real.log n ^ ((2 : ℝ) / 5)))}).toReal := by sorry

end TreeCorrMatch.ErrorFree
