-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_power_sum_ratio
-- name    : WangRenyiEntropy.Noninteger.power_sum_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:31.528054+00:00
-- url     : https://prove2.me/theorems/12ac01ea-1a9f-499f-9e79-6b7f47ab3d4e
-- title:
--   Lemma 2.1 — power-sum ratio bound
-- statement:
--   Let $\alpha>1/2$, $\alpha\ne1$ be any real order, including positive integers, and let $p$ be any probability law on an alphabet of size $d\ge1$. Then
--   $$\frac{F_{2\alpha-1}(p)}{F_\alpha(p)^2}\le d^{|1-1/\alpha|}.$$
--   Both power sums have positive order and the denominator is positive by normalization. The bound controls the relative-variance contribution without excluding zero coordinates or singleton alphabets.
--
--   Differences from the source:
--   - encoding: finite alphabet and nonnegative normalized real probability coordinates → Fin d with d ≥ 1 and the published IsLaw predicate, allowing zero coordinates; reason: relabeling preserves every finite nonempty alphabet and every probability law
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 6 / PDF 8, Lemma 2.1

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment

namespace WangRenyiEntropy.Noninteger

/-- Lemma 2.1, printed p.6 / PDF p.8. No noninteger restriction. -/
theorem power_sum_ratio (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≠ 1)
    (d : ℕ) (hd : 1 ≤ d) (p : Law d) :
    powerSum (2 * α - 1) p / (powerSum α p) ^ 2 ≤ Real.rpow d |1 - 1 / α| := by sorry

end WangRenyiEntropy.Noninteger
