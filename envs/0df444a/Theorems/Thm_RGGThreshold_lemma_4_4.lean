-- Prove2me | Theorems.Thm_RGGThreshold_lemma_4_4
-- name    : RGGThreshold.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:26.169068+00:00
-- url     : https://prove2.me/theorems/aa1f346c-0a61-4210-bc73-a3a52a5027bd
-- title:
--   Lemma 4.4 — $\Psi_k,\psi_k$ are within $O((1+t^4)/k)$ of $\Phi,\phi$
-- statement:
--   For an integer $k\ge3$ let $S_k$ be the law of $\sqrt k\,y(1)$, $y$ uniform on $\mathbb S^{k-1}\subset\mathbb R^k$, with distribution function $\Psi_k$ and density $\psi_k$. There is an absolute constant $C$ such that for every $k\ge3$ and every real $t$,
--
--   $$
--   |\Psi_k(t)-\Phi(t)|\le C\,\frac{1+t^4}{k}\,\Phi(t),\qquad |\psi_k(t)-\phi(t)|\le C\,\frac{1+t^4}{k}\,\phi(t).
--   $$
--
--   This relative comparison lets the paper replace sphere probabilities by Gaussian ones with a multiplicative error.
--
--   **Formalization Note** $\psi_k$ is the continuous version of the density (definition `sphCDF`).
--
--   Differences from the source:
--
--   - reading: O((1+t⁴)/k) in each inequality → one absolute constant C for both, chosen before k and t; reason: O(·) is a constant independent of k and t; taking the larger of two constants gives one
--   - encoding: "the PDF" ψ_k of S_k → the continuous closed-form version sphPDF; reason: a pointwise bound needs a fixed version of the density; this is the standard one
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 4.4, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RGGThreshold_gaussCDF
import Definitions.Def_RGGThreshold_sphCDF

namespace RGGThreshold

/-- **Lemma 4.4** (Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256 1a398ef9…,
Lemma 4.4, p.13 (PDF p.15)). For every integer `k ≥ 3` and every real `t`,
`|Ψ_k(t) - Φ(t)| ≤ O((1 + t⁴)/k) Φ(t)` and `|ψ_k(t) - ϕ(t)| ≤ O((1 + t⁴)/k) ϕ(t)`, where `S_k` is the
law of `√k · y(1)` for `y` uniform on `S^{k-1} ⊂ ℝ^k`, with distribution function `Ψ_k` and density
`ψ_k`.

**Formalization Note** `O(·)` is one absolute constant `C`, chosen before `k` and `t`, for both
inequalities. `ψ_k` is the continuous version of the density (`sphPDF`). -/
theorem lemma_4_4 : ∃ C : ℝ, ∀ k : ℕ, 3 ≤ k → ∀ t : ℝ,
    |sphCDF k t - gaussCDF t| ≤ C * ((1 + t ^ 4) / k) * gaussCDF t ∧
    |sphPDF k t - gaussPDF t| ≤ C * ((1 + t ^ 4) / k) * gaussPDF t := by sorry

end RGGThreshold
