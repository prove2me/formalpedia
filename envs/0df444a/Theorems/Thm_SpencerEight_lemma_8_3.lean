-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_3
-- name    : SpencerEight.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:05.036196+00:00
-- url     : https://prove2.me/theorems/a6429414-abb4-4612-8714-3269a9715b50
-- title:
--   Lemma 8.3 — lossless partial signs
-- statement:
--   Let $K\subseteq\mathbb R^m$, $m\ge1$, be symmetric and convex with $\gamma_m(K)\ge e^{-Em}$. If $0<q<1$ and
--   $$\log2-E>h\bigl((1-q)/2\bigr),$$
--   there is $y\in\{-1,0,1\}^m$ supported on more than $(1-q)m$ coordinates such that $s_\star y\in K$. The same holds for every amplitude $s$ satisfying Eq. (59). Moreover $E:=q^2/2$ is sufficient: $\log2-q^2/2>h((1-q)/2)$ for $0<q<1$.
--
--   This is the step that turns a lower bound on Gaussian mass into a partial signing, at no union-bound cost.
--
--   Differences from the source:
--   - reading: for K ⊆ ℝ^m; "for every m ≥ 1" in the last sentence → m ≥ 1 is a hypothesis of the whole statement; reason: at m = 0 "more than (1 − q)m coordinates" cannot hold, so the first sentence needs it too
--   - encoding: E := q²/2 is sufficient → the inequality log 2 − q²/2 > h((1 − q)/2) for 0 < q < 1; reason: this is exactly the lemma's hypothesis on E at E = q²/2, and E is universally quantified in the signing statement
--   - encoding: any amplitude s satisfying Eq. (59) → s with ∃ a δ, Eq59 s a δ; reason: Eq. (59) is a condition on (s, a, δ)
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.3, p.71 (PDF p.71)

import Mathlib
import Definitions.Def_SpencerEight_LosslessPartialSigning
import Definitions.Def_SpencerEight_CodingAmplitude
import Definitions.Def_SpencerEight_sStar

namespace SpencerEight

/-- Lemma 8.3 (Lossless partial signs), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.71 (PDF p.71). The statement at `s⋆`; the same at every amplitude satisfying Eq. (59); and the sufficiency of `E := q²/2`, namely `log 2 − q²/2 > h((1 − q)/2)`, which is the lemma's hypothesis on `E`, for every `m ≥ 1`. -/
theorem lemma_8_3 :
    LosslessPartialSigning sStar ∧
    (∀ s : ℝ, CodingAmplitude s → LosslessPartialSigning s) ∧
    (∀ q : ℝ, 0 < q → q < 1 → Real.binEntropy ((1 - q) / 2) < Real.log 2 - q ^ 2 / 2) := by sorry

end SpencerEight
