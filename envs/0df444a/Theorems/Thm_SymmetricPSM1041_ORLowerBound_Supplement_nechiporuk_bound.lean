-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_nechiporuk_bound
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.nechiporuk_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:50:36.163463+00:00
-- url     : https://prove2.me/theorems/67d657c3-a6a2-471f-bc62-f17149ac26e6
-- title:
--   Theorem 29 — Nechiporuk bound
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$, let $S\subseteq[n]$, and let $N_S(f)$ be the number of subfunctions of $f$ on $S$. Every perfectly correct, support-private PSM protocol $P$ for $f$, with local alphabet sizes $K_i=|\mathcal A_i(P)|$, satisfies
--
--   $$\sum_{i\in S}\log_2 K_i\ \ge\ \log_2 N_S(f)-1.$$
--
--   Here $\mathcal A_i(P)$ is the set of messages party $i$ actually sends. Summed over the blocks of a partition, this recovers the Nechiporuk-type bound on $C_{\rm indiv\text{-}sum}$ (Corollary 30).
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: local alphabet sizes K_i → K_i = card of the actual local alphabet localAlphabet P i; reason: the actual alphabet is contained in the declared one, so a lower bound on Σ log₂ of actual sizes implies the one for declared sizes
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 19, Theorem 29 (proof pp. 19–20)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ColoringsSubfunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem nechiporuk_bound {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (P : PSM (Fin n)) (hcorr : PerfectCorrect P f) (hpriv : SupportPrivate P f) :
    Real.logb 2 (subfunctionCount f S : ℝ) - 1 ≤
      ∑ i ∈ S, Real.logb 2 ((localAlphabet P i).card : ℝ) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
