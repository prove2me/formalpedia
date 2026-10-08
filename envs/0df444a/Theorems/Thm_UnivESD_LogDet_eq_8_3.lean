-- Prove2me | Theorems.Thm_UnivESD_LogDet_eq_8_3
-- name    : UnivESD.LogDet.eq_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:16:20.703504+00:00
-- url     : https://prove2.me/theorems/8435793d-ecd8-47c9-80eb-65403bdc0294
-- title:
--   (8.3), p. 2055 — $\mathbf P(\sigma_{n-i}\le ci/n)=O(\exp(-n^{0.01}))$ for $2n^{0.99}\le i\le n-1$ (corrected range)
-- statement:
--   Let $A_n=M_n+X_n$ be as in Theorem 1.5 and fix $z\in\mathbb C$. Write $\sigma_j=\sigma_j\big(\tfrac1{\sqrt n}A_n-zI\big)$, $1\le j\le n$. Then there are constants $c>0$ and $C$, independent of $n$ and $i$, such that
--   $$\mathbf P\Big(\sigma_{n-i}\le c\,\frac in\Big)\le C\exp(-n^{0.01})$$
--   for all $n$ and all integers $i$ with $2n^{0.99}\le i\le n-1$.
--
--   Through the union bound and the Borel–Cantelli lemma this controls, almost surely, the contribution of the small singular values to $\frac1n\sum_i\log\sigma_i$; it is the probabilistic input of both (8.2) and the $\kappa\log(1/\kappa)$ bound on p. 2057.
--
--   **Formalization Note** The paper prints the range $1\le i\le n-n^{0.99}$. That is false for small $i$: for Gaussian $x$ and $M_n=0$, $n\,\sigma_{n-1}(\tfrac1{\sqrt n}A_n)$ converges in law to a non-degenerate distribution on $(0,\infty)$, so $\mathbf P(\sigma_{n-1}\le c/n)$ stays bounded away from $0$. The paper's proof deletes $k=i/2$ rows and needs codimension $k\gtrsim n^{0.99}$, and its use concerns $i\ge n^{0.99}$; the statement is posed on $2n^{0.99}\le i\le n-1$. The constants may depend on $z$, $x$ and the sequence $M_n$. The event's probability is the outer measure.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, pp. 2055–2056 (PDF 33–34), §8, proof of Theorem 1.15, (8.3)

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic
import Definitions.Def_UnivESD_LogDet_Model

open MeasureTheory ProbabilityTheory

namespace UnivESD.LogDet

/-- (8.3), Tao–Vu, Ann. Probab. 38 (2010), §8, p. 2055, on the corrected range. For `A_n` as in
Theorem 1.5 and every fixed `z ∈ ℂ` there are constants `c > 0` and `C` (depending on `z` and the
data, not on `n` or `i`) such that, with `σ_j = σ_j(A_n/√n − zI)` one-based,
`P(σ_{n−i} ≤ c i/n) ≤ C exp(−n^{0.01})` for all `n` and all `2 n^{0.99} ≤ i ≤ n − 1`.

Formalization Note: printed for `1 ≤ i ≤ n − n^{0.99}`, which is false for small `i`
(for Gaussian `x` and `M_n = 0`, `n σ_{n−1}` has a non-degenerate limit law); the proof
(`k = i/2` deleted rows, codimension `≳ n^{0.99}`) and its use need only `i ≥ 2n^{0.99}`. -/
theorem eq_8_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hxs : IIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : HSBound M) (z : ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n i : ℕ, 2 * (n : ℝ) ^ (0.99 : ℝ) ≤ (i : ℝ) → i ≤ n - 1 →
      P {ω | sv (shiftA M xs z n ω) (n - i) ≤ c * (i : ℝ) / (n : ℝ)} ≤
        ENNReal.ofReal (C * Real.exp (-(n : ℝ) ^ (0.01 : ℝ))) := by sorry

end UnivESD.LogDet
