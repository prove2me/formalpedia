-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_2_7
-- name    : PriceIgnorance.Pairwise.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:10.916213+00:00
-- url     : https://prove2.me/theorems/585f0a2a-283f-48d1-aacd-b71ea32c9069
-- title:
--   Lemma 2.7 — $|\mathbb E_Df-\mathbb E_{\widehat D}f|\le2\|f\|_\infty\,d_{TV}(D,\widehat D)$
-- statement:
--   Let $\Omega$ be a set, $f:\Omega\to\mathbb R$ a bounded function, and $D,\widehat D$ discrete distributions on $\Omega$. Then
--   $$\Big|\mathbb E_{X\sim D}[f(X)]-\mathbb E_{Y\sim\widehat D}[f(Y)]\Big|\ \le\ 2\,\|f\|_\infty\, d_{TV}(D,\widehat D),$$
--   where $\|f\|_\infty=\sup_\omega|f(\omega)|$ and $d_{TV}(D,\widehat D)=\frac12\sum_\omega|D(\omega)-\widehat D(\omega)|$.
--
--   In Theorem 3.16 this bounds the change in a bounded algorithm's value when the witness law is replaced by the empirical law of the hidden samples.
--
--   Differences from the source:
--   - encoding: distributions D, D^ on Ω (discrete, as the preceding paragraph says) → PMFs on Ω; E as Σ_ω D(ω) f(ω) (a tsum); d_TV the published QCSepTotal.tv; reason: discrete probability measures are PMFs; for bounded f the series converges absolutely
--   - encoding: f bounded, ‖f‖_∞ → ∃ M, ∀ ω, |f ω| ≤ M; ‖f‖_∞ = ⨆ ω, |f ω|; reason: the real supremum of a bounded family is its sup
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Lemma 2.7 (proof pp. 25–26)

import Mathlib
import Definitions.Def_QCSepTotal_tv
import Definitions.Def_PriceIgnorance_Pairwise_Empirical

namespace PriceIgnorance.Pairwise

/-- Lemma 2.7 (p. 4): for a bounded `f : Ω → ℝ` and distributions `D`, `D̂` on `Ω`,
`|E_{X∼D}[f(X)] − E_{Y∼D̂}[f(Y)]| ≤ 2 ‖f‖_∞ d_TV(D, D̂)`. -/
theorem lemma_2_7 {Ω : Type*} (f : Ω → ℝ) (hf : ∃ M : ℝ, ∀ ω, |f ω| ≤ M) (D Dh : PMF Ω) :
    |pmfExp D f - pmfExp Dh f| ≤ 2 * supNorm f * QCSepTotal.tv D Dh := by sorry

end PriceIgnorance.Pairwise
