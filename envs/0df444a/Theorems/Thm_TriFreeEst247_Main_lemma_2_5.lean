-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_2_5
-- name    : TriFreeEst247.Main.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:25.32883+00:00
-- url     : https://prove2.me/theorems/01e1e31e-d45a-4fde-9bf6-19d5b01d432f
-- title:
--   Lemma 2.5: estimating a dense CSP optimum
-- statement:
--   There are absolute $C>0$ and $d\in\mathbb N$ with the following property. For every finite alphabet $A$ with $|A|\ge2$, every $n\ge3$, and $0<\zeta<1$, an algorithm chosen independently of the CSP uses at most $q$ whole-local-function queries, where
--
--   $$q\le C\zeta^{-d}(\log|A|)^d.$$
--
--   For every dense normalized $Q$ on these variables and labels, its real output $Z$ satisfies
--
--   $$\Pr[|Z-\mathrm{OPT}_{\mathrm{CSP}}(Q)|\le\zeta]\ge5/6.$$
--
--   The query bound is independent of $n$ and $Q$. This supplies the optimum-estimation guarantee needed after compression.
--
--   Differences from the source:
--   - encoding: finite CSP variable sets and alphabets → Fin n vertices, finite alphabet types, and attained finite real suprema; reason: bijections and finite nonempty maxima preserve all instances
--   - reading: poly(1/ζ, log |A|) → C ζ⁻ᵈ (log |A|)ᵈ with absolute C,d and natural log; reason: the polynomial and O constants are absolute and quantified before every varying parameter
--   - encoding: randomized local-function query algorithm → PMF over the shared decision trees with each whole function as an answer; reason: the finite-sampling algorithm provides such a distribution and does not access Q before querying it
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.8, Lemma 2.5

import Mathlib
import Definitions.Def_TriFreeEst247_Main_GraphModel
import Definitions.Def_TriFreeEst247_Main_DenseCSP

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_2_5 :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ (A : Type) [Fintype A], 2 ≤ Fintype.card A →
      ∀ n : ℕ, 3 ≤ n → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
        ∃ q : ℕ, (q : ℝ) ≤ C * ζ⁻¹^d * (Real.log (Fintype.card A : ℝ))^d ∧
        ∃ alg : CSPAlgorithm n A, QAlgorithms.RandMakesAtMost alg q ∧
          ∀ Q : CSP n A, isDense Q →
            (5 / 6 : ℝ≥0∞) ≤ outputProb alg (cspOracle Q) (fun z => |z - cspOpt Q| ≤ ζ)
    := by sorry

end TriFreeEst247.Main
