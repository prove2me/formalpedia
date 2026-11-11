-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_46
-- name    : RamseyLST.Main.lemma_46
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:11.552446+00:00
-- url     : https://prove2.me/theorems/e889f128-f7b2-4772-98aa-073d12c11625
-- title:
--   Lemma 46 — the exponent algebra: $\hat\psi(\Phi^\star)(1 - \log t/t) = 1 - O((\log t + \log\log(4\Phi^\star))/t)$
-- statement:
--   Let $\sigma>1$. There is a constant $C$ such that for every real $t\ge1$ and every $\Phi^\star\ge\sigma$, with $q=2^t$ and $\hat\psi(\Phi^\star)=\psi_1(\Phi^\star)+\psi_2+\psi_3-2$ (where $\psi_1(\Phi)=(t\log_\sigma\Phi)^{-2/t}$, $\psi_2=(\log q)^{-1/t}$, $\psi_3=1-1/t$),
--
--   $$1-C\,\frac{\log t+\log\log(4\Phi^\star)}{t}\ \le\ \hat\psi(\Phi^\star)\Big(1-\frac{\log t}{t}\Big)\ \le\ 1,$$
--
--   with all logarithms in base 2.
--
--   This identifies the exponent produced by the hierarchical petal decomposition (Lemma 40, combined with Lemma 32 for $q=2^t$) with the exponent $1-O\big((\log t+\log\log(4\Phi))/t\big)$ of Theorem 25.
--
--   Differences from the source:
--   - generalization: σ = 800, the absolute constant of Remark 1 → every real σ > 1, with the constant C allowed to depend on σ; reason: for σ = 800 the constant C is absolute, so the statement specializes to the paper's
--   - reading: ψ̂(Φ⋆)(1 − log t/t) = 1 − O((log t + log log(4Φ⋆))/t) → 1 − C(log t + log log(4Φ⋆))/t ≤ ψ̂(Φ⋆)(1 − log t/t) ≤ 1, with one existential C; reason: the O(·) term is a nonnegative error bounded by C(·)/t, as the proof shows (ψ̂(Φ⋆) ≤ 1); this is the stronger of the readings of '= 1 − O(·)'
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 56 (PDF 60), Lemma 46; proof p. 97 (PDF 101)

import Mathlib
import Definitions.Def_RamseyLST_Main_Weights

namespace RamseyLST.Main

/-- Lemma 46 (p. 56): for every `σ > 1` there is a constant `C` such that for every `t ≥ 1` and
every `Φ⋆ ≥ σ`, with `q = 2^t`,
`1 − C (log t + log log(4Φ⋆))/t ≤ ψ̂(Φ⋆)(1 − log t / t) ≤ 1` (logarithms in base 2). -/
theorem lemma_46 (σ : ℝ) (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ Φ : ℝ, σ ≤ Φ →
      1 - C * (Real.logb 2 t + Real.logb 2 (Real.logb 2 (4 * Φ))) / t ≤
          psiHat σ ((2 : ℝ) ^ t) t Φ * (1 - Real.logb 2 t / t) ∧
        psiHat σ ((2 : ℝ) ^ t) t Φ * (1 - Real.logb 2 t / t) ≤ 1 := by sorry

end RamseyLST.Main
