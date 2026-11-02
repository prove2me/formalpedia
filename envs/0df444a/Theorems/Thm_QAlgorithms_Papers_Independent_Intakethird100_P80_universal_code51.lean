-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_universal_code51
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.universal_code51
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:28:10.948458+00:00
-- url     : https://prove2.me/theorems/46debd21-2589-47de-8c98-6395ea78d24a
-- title:
--   Binary universal block code with logarithmic regret
-- statement:
--   Fix a finite nonlocality scenario and a normalized setting law $\sigma$. Let $\mathcal P_\sigma$ be its full family of potential-outcome local trial laws. There exist actual binary prefix block codes $C_n$ on the entire finite trial-word alphabet, a constant $K>0$, and an integer $N\ge2$, such that every $n\ge N$ and every word $z^n$ satisfy
--
--   $$|C_n(z^n)|\le\inf_{\pi\in\Pi}\left[-\log_2\prod_{i=1}^n P_{\sigma;\pi}(z_i)\right]+K\log_2 n.$$
--
--   An impossible word has infinite ideal length. The codes also exist for the smaller block lengths; the bound is asymptotic. Both constants are chosen before the block length and the sample word. This is the source's local-family specialization, not a claim for an arbitrary composite statistical class.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 27, Appendix IV-A.3: universal code with logarithmic regret

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

section ProbabilityCoding

/-- PDF p.27, (51), specialized to the local family of pp.29–31: actual binary initialTrials codes
for the FULL alphabet, uniform in n and in the data. Impossible likelihoods have length infinity.
A threshold n>=2 expresses O(log n); both constants precede all n and sample words. -/
theorem universal_code51 (S : BellExperiment) (s : Sigma S) :
    ∃ (C : (n : ℕ) → (Fin n → BellTrial S) → List Bool) (K : ℝ) (N : ℕ),
      0 < K ∧ 2 ≤ N ∧ (∀ n, IsPrefixCode (C n)) ∧
      ∀ n, N ≤ n → ∀ z : Fin n → BellTrial S,
        ENNReal.ofReal ((C n z).length : ℝ) ≤
          (⨅ p : PiLocal S, idealLength (trialJointLaw (localTable p.1) s.1) z) +
          ENNReal.ofReal (K * Real.logb 2 n) := by sorry

end ProbabilityCoding

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
