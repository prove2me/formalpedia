-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_2_10
-- name    : RobustKellyTV.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:32.984413+00:00
-- url     : https://prove2.me/theorems/2ae5c993-1920-4c8a-a447-6142142e4f88
-- title:
--   Theorem 2.10 — $\mathbb E_S\tau_\alpha(M^{\mathrm{CK}})\sim\log(1/\alpha)/\Gamma(S)$ as $\alpha\downarrow0$
-- statement:
--   Assume the standing assumptions and the Laplace pseudocounts. Fix a full-support $S\in\Delta_d\setminus\mathcal P_0$ and let $\tau^{\mathrm{CK}}_\alpha=\tau_\alpha(M^{\mathrm{CK}})$. Then, as $\alpha\downarrow0$,
--
--   $$\mathbb E_S\tau^{\mathrm{CK}}_\alpha\sim\frac{\log(1/\alpha)}{\Gamma(S)} .$$
--
--   The adaptive clipped-Kelly test attains the exact first-order Wald constant.
--
--   Differences from the source:
--   - encoding: i.i.d. observations X_1, X_2, … from S → the infinite product law of S on ℕ → Fin d, with X_t the coordinate t − 1; reason: every process is a function of the observed prefix, so no instance changes
--   - encoding: E_S τ → a lintegral of τ (valued in ℕ∞) in [0, ∞]; reason: an infinite expectation is kept as ∞ and cannot read as 0
--   - encoding: E_S τ ∼ log(1/α)/Γ(S) as α ↓ 0 → the [0, ∞]-valued ratio E_S τ / (log(1/α)/Γ(S)) tends to 1 as α → 0⁺; reason: the meaning of ∼; the ratio is not truncated
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.3, Theorem 2.10, eq. (23), p.10 (proof pp.27–29)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_seqLaw
import Definitions.Def_RobustKellyTV_Mck

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustKellyTV

/-- **Theorem 2.10** (Expected stopping time of adaptive clipped Kelly). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 2.10,
eq. (23), p.10.

Assume the pseudocounts (16). Fix a full-support `S ∉ P0` and let `τ^CK_α = τ_α(M^CK)`. Then, as
`α ↓ 0`, `E_S τ^CK_α ∼ log(1/α)/Γ(S)`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `E_S τ` is a `lintegral` in `[0, ∞]`, and `∼` is the statement that
the `[0, ∞]`-valued ratio `E_S τ^CK_α / (log(1/α)/Γ(S))` tends to `1` as `α → 0⁺`; an infinite
expectation therefore cannot pass. -/
theorem theorem_2_10 {d : ℕ} (σ : Setting d) (S : stdSimplex ℝ (Fin d))
    (hSP : (S : Fin d → ℝ) ∉ nullBall σ) (hSpos : ∀ i, 0 < (S : Fin d → ℝ) i) :
    Tendsto (fun α : ℝ =>
        (∫⁻ ω, (stopTime (Mck σ (laplace d)) α ω : ℝ≥0∞) ∂(seqLaw S)) /
          ENNReal.ofReal (Real.log (1 / α) / Gamma σ S))
      (𝓝[>] 0) (𝓝 1) := by sorry

end RobustKellyTV
