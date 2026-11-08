-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_65
-- name    : SpencerEight.lemma_8_65
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:29.143751+00:00
-- url     : https://prove2.me/theorems/979b93e5-b833-474d-a3e3-f62b1b276ec5
-- title:
--   Lemma 8.65 — the first row with a unit-charge shared constraint
-- statement:
--   Let $B_i$ be symmetric contractions in $\mathbb R^{n\times n}$, $w,L>0$ and $0<m\le wn$. Set $G:=\sum_{i=1}^m\xi_iB_i$ and $r_0:=\sqrt{wn/\eta_0}$, and suppose $L^2s_+^2\eta_0\ge w$, where $\eta_0=0.065$, $H_0=4.338$, $e_0=0.007955$ and $M_3=0.011088253617755063971661323336071274275573242$. Then the set
--   $$K_3:=\bigl\{\xi:\|G\|\le r_0,\ \operatorname{tr}[f_3(G/(s_+L\sqrt n))]\le(1+\delta_{\mathrm{mom}})nM_3\bigr\}$$
--   is symmetric and convex, and
--   $$\gamma_m[K_3]\ge\exp\Bigl\{-\frac{me_0}{w}-\frac{H_0}{H_0-1}\Bigr\}.$$
--
--   The charge $H_0/(H_0-1)$ is not multiplied by $m$. This is the row of the first signing phase.
--
--   Differences from the source:
--   - reading: B_i symmetric contractions, dimension unstated → B_i in ℝ^{n×n}; reason: Section 8 pads to order n, and the trace statistic is normalized by n
--   - encoding: tr[f₃(X)] with f₃ = +∞ for |u| ≥ 1 → an ℝ≥0∞-valued sum over the eigenvalues; the threshold is ENNReal.ofReal of a nonnegative number; reason: +∞ is representable, and the sublevel set is the same
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.65, p.128 (PDF p.128); constants Section 8.19, p.119 (PDF p.119), Section 8.22, p.131 (PDF p.131)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_deltaMom
import Definitions.Def_SpencerEight_traceF3
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.65 (The first row with a unit-charge shared constraint), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.128 (PDF p.128).

**Formalization Note** The constants are written as printed: `η₀ = 0.065`, `H₀ = 4.338`, `e₀ = 0.007955` (Section 8.22, p.131), `M₃ = 0.011088253617755063971661323336071274275573242` (Section 8.19, p.119). The charge `H₀/(H₀ − 1)` is not multiplied by `m`. The trace statistic is extended-valued (`traceF3`). -/
theorem lemma_8_65 {n m : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, IsSymmContraction (B i)) {w L : ℝ} (hw : 0 < w) (hL : 0 < L) (hm0 : 0 < m)
    (hm : (m : ℝ) ≤ w * n) (hrad : w ≤ L ^ 2 * sPlus ^ 2 * 0.065) :
    let K₃ : Set (Fin m → ℝ) := {ξ |
      ‖signedSum B ξ‖ ≤ Real.sqrt (w * n / 0.065) ∧
      traceF3 ((sPlus * L * Real.sqrt n)⁻¹ • signedSum B ξ) ≤
        ENNReal.ofReal
          ((1 + deltaMom) * n * 0.011088253617755063971661323336071274275573242)}
    Convex ℝ K₃ ∧ (∀ ξ ∈ K₃, -ξ ∈ K₃) ∧
    ENNReal.ofReal (Real.exp (-((m : ℝ) * 0.007955 / w) - 4.338 / (4.338 - 1))) ≤
      gammaM (Fin m) K₃ := by sorry

end SpencerEight
