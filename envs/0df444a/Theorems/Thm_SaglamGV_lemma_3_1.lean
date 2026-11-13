-- Prove2me | Theorems.Thm_SaglamGV_lemma_3_1
-- name    : SaglamGV.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:51.19388+00:00
-- url     : https://prove2.me/theorems/81733e07-cf68-4443-af21-c931d50ffadf
-- title:
--   Lemma 3.1 — Fourier estimates for the punctured Hamming ball
-- statement:
--   Let $w=d-1$ and $\mu=1_{B_d}/V$. Fix $\varepsilon>0$ and suppose $\lg n\ll w\le(1/2-\varepsilon)n$. Then
--
--   $$
--   \mathbb E_y|\hat\mu(y)|^3=O\Big(\frac1{Vn^3}\Big)
--   \qquad\text{and}\qquad
--   \Pr_y\big[|\hat\mu(y)|>1/n\big]\le2^{-n+\frac{2n\lg n}{w}\lg\left(\frac{ew}{\lg n}\right)} .
--   $$
--
--   Precisely: for every $\varepsilon>0$ there are $L$, $C$ and $N_0$ depending only on $\varepsilon$ such that both bounds (the first with constant $C$) hold for all $n\ge N_0$ and all $w$ with $L\lg n\le w\le(1/2-\varepsilon)n$.
--
--   These are the two analytic inputs to the transition estimate: the third moment controls the region $|\tau\hat\mu|\le1$, the tail bound the rest.
--
--   Differences from the source:
--   - encoding: lg n ≪ w and O(1/(Vn³)) → ∃ L, C, N₀ depending on ε only, for all n ≥ N₀ and L·lg n ≤ w ≤ (1/2 − ε)n; reason: equivalent to the sequential reading (for every sequence with w/lg n → ∞ the bounds hold eventually with one constant)
--   - encoding: E_y, Pr_y and µ̂ → avgY, probY over 𝔽₂ⁿ (y = 0 included) and the unnormalized fhat; reason: the paper's normalization (§3.1)
--   - encoding: w = d − 1 → d = w + 1 with w : ℕ; reason: avoids natural-number subtraction
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Lemma 3.1, p.4 (derived in Appendix A, pp.6–7)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Walk
import Definitions.Def_SaglamGV_Fourier

namespace SaglamGV

/-- Lemma 3.1, Fourier estimates for the punctured Hamming ball (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), Lemma 3.1, p.4).

Let $w = d − 1$ and $μ = 1_{B_d}/V$. Fix $ε > 0$ and suppose $\lg n ≪ w ≤ (1/2 − ε)n$. Then
$E_y|\hat μ(y)|^3 = O(1/(Vn^3))$ and
$\Pr_y[|\hat μ(y)| > 1/n] ≤ 2^{−n + (2n \lg n / w) \lg(ew/\lg n)}$.

**Formalization Note** "$\lg n ≪ w$" and $O(·)$ are encoded uniformly: there are $L, C, N_0$
depending on $ε$ only such that both bounds hold for all $n ≥ N_0$ and $L \lg n ≤ w ≤ (1/2−ε)n$
(equivalent to the sequential reading). $\hat μ$ is unnormalized, $E_y$, $\Pr_y$ are uniform over
$𝔽_2^n$, and $y = 0$ is included. -/
theorem lemma_3_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ L C : ℝ, ∃ N₀ : ℕ, ∀ n w : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      avgY (fun y => |muHat n (w + 1) y| ^ 3) ≤ C / ((vol n (w + 1) : ℝ) * (n : ℝ) ^ 3) ∧
      probY (fun y => 1 / (n : ℝ) < |muHat n (w + 1) y|) ≤
        (2 : ℝ) ^ (-(n : ℝ) + 2 * n * Real.logb 2 n / w *
          Real.logb 2 (Real.exp 1 * w / Real.logb 2 n)) := by sorry

end SaglamGV
