-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P31_measuredBB84_uncertainty
-- name    : QAlgorithms.Papers.Independent.Claimed50.P31.measuredBB84_uncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:23:51.203096+00:00
-- url     : https://prove2.me/theorems/7c1742c4-0372-4c8b-a3d5-d96b6f120c7b
-- title:
--   Measured BB84 uncertainty with explicit smoothing and positivity
-- statement:
--   Let $n\ge0$ be an integer. Independently choose uniform strings $X\in\{0,1\}^n$ and $B\in\{+,\times\}^n$, encode $X$ in the BB84 product state $|X\rangle_B$, and apply any fixed measurement with classical outcome $K$. The measurement operation is independent of $X,B$; its outcome need not be independent. For $0<\varepsilon\le1$, write $H_{\min}^{\varepsilon}$ for worst-case classical conditional min-entropy, in bits, smoothed by deleting an event of probability at most $\varepsilon$, without renormalizing. Then
--
--   $$H_{\min}^{\varepsilon}(X\mid B,K)\ge \frac n2-10\sqrt[3]{n^2\log_2(1/\varepsilon)}.$$
--
--   The displayed lower bound is strictly positive whenever $n>8000\log_2(1/\varepsilon)$. The cube root is the nonnegative real root. This result supplies the measured uncertainty estimate used in the ROT analysis.
--
--   **Formalization Note** The experiment is constructed by uniform sampling followed by one fixed positive, normalized effect family. Its bundled Born laws allow arbitrary discrete classical outcome alphabets. Entropy takes values in the extended reals, including $+\infty$ when $\varepsilon=1$.
-- source:
--   Composable Security in the Bounded-Quantum-Storage Model, arXiv:0709.0492v1, PDF p. 6, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P31

open scoped ENNReal ComplexOrder

/-- Lemma 2.3, PDF p.6, with its Appendix A proof on PDF p.18.
The measurement is fixed before the independently uniform encoding choices.
The conclusion includes the source's strict positivity clause. -/
theorem measuredBB84_uncertainty (n : ℕ) (K : Type*) [Nonempty K]
    (M : BB84Measurement n K) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) :
    let bound : ℝ := (n : ℝ) / 2 -
      10 * Real.rpow ((n : ℝ) ^ 2 * Real.logb 2 (1 / epsilon)) (1 / 3 : ℝ)
    (bound : EReal) ≤ eventSmoothMinEntropy (bb84Experiment M)
      (fun w => w.1) (fun w => w.2) epsilon ∧
    ((n : ℝ) > 8000 * Real.logb 2 (1 / epsilon) → 0 < bound) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P31

end
