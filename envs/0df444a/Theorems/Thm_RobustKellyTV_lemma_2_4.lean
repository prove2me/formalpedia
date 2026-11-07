-- Prove2me | Theorems.Thm_RobustKellyTV_lemma_2_4
-- name    : RobustKellyTV.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:25.787122+00:00
-- url     : https://prove2.me/theorems/4f399411-6267-41d2-978a-34308b2b36cb
-- title:
--   Lemma 2.4 — oracle mismatch is bounded by KL: $0\le\Gamma(S)-h(S,U)\le D_{\mathrm{KL}}(S\|U)$
-- statement:
--   Assume the standing assumptions. Let $S\in\Delta_d\setminus\mathcal P_0$ have full support and let $U\in\Delta_d$ have strictly positive coordinates. Then
--
--   $$0\le\Gamma(S)-h(S,U)\le D_{\mathrm{KL}}(S\|U),\qquad h(S,U)=\sum_iS_i\log E_U(i).$$
--
--   It converts log-loss regret of a predictor into regret of the robust e-process.
--
--   Differences from the source:
--   - encoding: D_KL(S‖U) ∈ [0, ∞] → its real value (toReal); reason: U has positive coordinates, so D_KL(S‖U) is finite
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.1, Lemma 2.4, eq. (14), p.8 (proof p.23)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_oracleE

namespace RobustKellyTV

/-- **Lemma 2.4** (Oracle mismatch is bounded by KL). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Lemma 2.4, eq. (14), p.8.

Let `S ∉ P0` have full support and let `U ∈ ∆_d` have strictly positive coordinates. Then
`0 ≤ Γ(S) − h(S, U) ≤ D_KL(S‖U)`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `D_KL(S‖U)` is finite because `U` has positive coordinates, so it is
compared as a real number (`toReal`). -/
theorem lemma_2_4 {d : ℕ} (σ : Setting d) (S U : Fin d → ℝ) (hS : S ∈ stdSimplex ℝ (Fin d))
    (hSP : S ∉ nullBall σ) (hSpos : ∀ i, 0 < S i) (hU : U ∈ stdSimplex ℝ (Fin d))
    (hUpos : ∀ i, 0 < U i) :
    0 ≤ Gamma σ S - hRet σ S U ∧ Gamma σ S - hRet σ S U ≤ (kl S U).toReal := by sorry

end RobustKellyTV
