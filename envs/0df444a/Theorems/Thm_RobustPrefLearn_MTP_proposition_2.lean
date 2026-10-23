-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_proposition_2
-- name    : RobustPrefLearn.MTP.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:13.038951+00:00
-- url     : https://prove2.me/theorems/24701062-4f7b-4605-af8e-87d216c2f7be
-- title:
--   Proposition 2, p. 17 — closed form of I^OA_* and its two-sided bounds
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. The value of $I^{\mathrm{OA}}_*$ is
--   $$I^{\mathrm{OA}}_*=(1-p)\log\tfrac1p\Bigl(1+\sum_{n=2}^K\frac{p^{n-1}}{1+2p+\dots+(n-1)p^{n-2}}\Bigr)^{-1},$$
--   and
--   $$(1-p)\log\tfrac1p\;K\,\bigl(K+2p(K-1)\bigr)^{-1}\le I^{\mathrm{OA}}_*\le(1-p)\log\tfrac1p\,(1+p)^{-1}.$$
--
--   It gives the optimal worst-case rate $1/I^{\mathrm{OA}}_*$ explicitly, and shows it is insensitive to $K$.
--
--   **Formalization Note** $I^{\mathrm{OA}}_*$ lives in $[0,\infty]$; the closed form is its value as a real number, and the bounds are stated on that real number. The denominator $1+2p+\dots+(n-1)p^{n-2}$ is $\sum_{i=1}^{n-1}ip^{i-1}$. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 17, Proposition 2

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Proposition 2, p. 17. `I^OA_* = (1 - p) log(1/p) (1 + ∑_{n=2}^K p^{n-1}/(1 + 2p + ⋯ + (n-1)p^{n-2}))^{-1}`,
and `(1 - p) log(1/p) K (K + 2p(K - 1))^{-1} ≤ I^OA_* ≤ (1 - p) log(1/p) (1 + p)^{-1}`. -/
theorem proposition_2 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IOA (K := K) p = ENNReal.ofReal ((1 - p) * Real.log (1 / p) *
      (1 + ∑ n ∈ Finset.Icc 2 K,
        p ^ (n - 1) / ∑ i ∈ Finset.Icc 1 (n - 1), (i : ℝ) * p ^ (i - 1))⁻¹) ∧
    (1 - p) * Real.log (1 / p) * (K : ℝ) * ((K : ℝ) + 2 * p * ((K : ℝ) - 1))⁻¹ ≤
      (1 - p) * Real.log (1 / p) *
        (1 + ∑ n ∈ Finset.Icc 2 K,
          p ^ (n - 1) / ∑ i ∈ Finset.Icc 1 (n - 1), (i : ℝ) * p ^ (i - 1))⁻¹ ∧
    (1 - p) * Real.log (1 / p) *
        (1 + ∑ n ∈ Finset.Icc 2 K,
          p ^ (n - 1) / ∑ i ∈ Finset.Icc 1 (n - 1), (i : ℝ) * p ^ (i - 1))⁻¹ ≤
      (1 - p) * Real.log (1 / p) * (1 + p)⁻¹ := by sorry

end RobustPrefLearn.MTP
