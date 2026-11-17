-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_G_8_commuting_loss
-- name    : SpectralFeedback.Supplement.theorem_G_8_commuting_loss
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:02:29.545137+00:00
-- url     : https://prove2.me/theorems/c292523f-8c96-4098-b852-734678aa06b2
-- title:
--   Theorem G.8 — strict commuting Gram-atom loss: $G^{\mathrm{com}}_{m,s}(\rho)<G_{m,s}(\rho)=\frac{s-1}s\operatorname{tr}\rho$
-- statement:
--   Let $m,s\ge2$, $d=ms$, and let $\rho\succeq0$ on $\mathbb C^d$ have spectrum
--
--   $$
--   (b+a,\ b^{[d-2]},\ b-a),\qquad 0<a<b .
--   $$
--
--   Let $G^{\mathrm{com}}_{m,s}$ restrict the atoms to be pairwise commuting. Then
--
--   $$
--   G^{\mathrm{com}}_{m,s}(\rho)<G_{m,s}(\rho)=\frac{s-1}{s}\operatorname{tr}\rho .
--   $$
--
--   For $s=2$ and $T=\operatorname{tr}\rho$, the quantitative bound
--
--   $$
--   G^{\mathrm{com}}_{m,2}(\rho)\le\frac T2-\min\Bigl\{\frac{b-a}{2},\ \frac{a^2}{16T}\Bigr\}\qquad\text{(G.8)}
--   $$
--
--   holds. Both maxima exist. The bound is a lower bound on the separation, not an exact formula for the commuting optimum.
--
--   Differences from the source:
--   - encoding: G_{m,s}(ρ) and G^com_{m,s}(ρ) → IsGreatest of rewardSet and of comRewardSet (with F = χ_s); reason: the paper's proof states that the commuting feasible set is compact, so its maximum exists
--   - encoding: ρ of dimension d = ms with the stated spectrum → ρ : Matrix (Fin (m·s)) (Fin (m·s)) ℂ with eigDesc ρ i the stated entries; reason: same matrices
--   - encoding: tr ρ → the real part of the complex trace; reason: the trace of a Hermitian matrix is real
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem G.8, (G.8), pp.103–104 (PDF pp.105–106)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi
import Definitions.Def_SpectralFeedback_Supplement_comRewardSet

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem G.8** (Strict commuting Gram-atom loss at every message budget; Qi, *Spectral Structure
and Exact Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026),
pp.103–104 (PDF pp.105–106)). Let `d = ms`, `m, s ≥ 2`, and let `ρ` have spectrum
`(b + a, b^{[d−2]}, b − a)`, with `0 < a < b`. Let `G^com_{m,s}` restrict the atoms to be pairwise
commuting. Then `G^com_{m,s}(ρ) < G_{m,s}(ρ) = ((s − 1)/s) tr ρ`. For `s = 2` and `T = tr ρ`, the
quantitative bound `G^com_{m,2}(ρ) ≤ T/2 − min{(b − a)/2, a²/(16T)}` (G.8) holds.

**Formalization Note** `ρ` acts on `ℂ^{ms}` (type `Fin (m * s)`); its full spectrum is
`eigDesc ρ i`, `i < ms` (0-based). `G_{m,s}(ρ) = v` is `IsGreatest (rewardSet s (chi s) m ρ) v`,
`G^com_{m,s}(ρ) = v` is `IsGreatest (comRewardSet s (chi s) m ρ) v` (the commuting maximum exists,
as the proof states: the commuting feasible set is compact). `tr ρ` is the real part of the complex
trace. -/
theorem theorem_G_8_commuting_loss (m s : ℕ) (hm : 2 ≤ m) (hs : 2 ≤ s)
    (ρ : Matrix (Fin (m * s)) (Fin (m * s)) ℂ) (hρ : ρ.PosSemidef) (a b : ℝ) (ha : 0 < a)
    (hab : a < b)
    (hspec : eigDesc ρ 0 = b + a ∧ (∀ i, 1 ≤ i → i ≤ m * s - 2 → eigDesc ρ i = b) ∧
      eigDesc ρ (m * s - 1) = b - a) :
    IsGreatest (rewardSet s (chi s) m ρ) (((s : ℝ) - 1) / s * ρ.trace.re) ∧
      ∃ vc : ℝ, IsGreatest (comRewardSet s (chi s) m ρ) vc ∧
        vc < ((s : ℝ) - 1) / s * ρ.trace.re ∧
        (s = 2 → vc ≤ ρ.trace.re / 2 - min ((b - a) / 2) (a ^ 2 / (16 * ρ.trace.re))) := by sorry

end Supplement

end SpectralFeedback
