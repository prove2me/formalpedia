-- Prove2me | Theorems.Thm_SphereGRF_Spectral_stein_weiss_weighted_l2
-- name    : SphereGRF.Spectral.stein_weiss_weighted_l2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:48.720765+00:00
-- url     : https://prove2.me/theorems/1e062964-2f27-48bc-b306-b2395c106475
-- title:
--   Stein–Weiss, cited in the proof of Theorem 3.1, p. 12 — $(\ell^2(w_0),\ell^2(w_1))_{\theta,2} = \ell^2(w_0^{1-\theta}w_1^\theta)$ with equivalent norms
-- statement:
--   Let $0 < \theta < 1$. There are constants $c_1, c_2 > 0$, depending only on $\theta$, such that for all weights $w_0, w_1 : \mathbb N_0 \to (0,\infty)$ and every real sequence $a = (a_\ell)$
--
--   $$
--   c_1 \sum_{\ell=0}^\infty w_0(\ell)^{1-\theta}w_1(\ell)^\theta\,a_\ell^2 \le \int_0^\infty t^{-2\theta}K(t,a)^2\,\frac{dt}{t} \le c_2 \sum_{\ell=0}^\infty w_0(\ell)^{1-\theta}w_1(\ell)^\theta\,a_\ell^2,
--   $$
--
--   where $K(t,a) = \inf_{a=b+c}\big(\|b\|_{\ell^2(w_0)} + t\|c\|_{\ell^2(w_1)}\big)$. Both sides are in $[0,+\infty]$; in particular the real interpolation space $(\ell^2(w_0), \ell^2(w_1))_{\theta,2}$ equals $\ell^2(w_0^{1-\theta}w_1^\theta)$ with equivalent norms.
--
--   The paper applies this theorem (Theorem 5.4.1 in Bergh and Löfström, 1976) to the weights of $\ell_n$ and $\ell_{n+1}$; combined with the integer case of Theorem 3.1 and the interpolation property it yields the fractional case.
--
--   **Formalization Note** All quantities take values in $[0,+\infty]$, so the statement covers sequences outside the spaces (both sides are then $+\infty$). The constants are chosen before the weights.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, proof of Theorem 3.1, p. 12 ('Applying the interpolation theorem of Stein–Weiss [see, e.g., Theorem 5.4.1 in Bergh and Löfström (1976)]')

import Mathlib
import Definitions.Def_SphereGRF_Spectral_WeightedSeqInterp

open scoped ENNReal

namespace SphereGRF.Spectral

/-- Interpolation theorem of Stein–Weiss for weighted `ℓ²` (cited in the proof of Theorem 3.1,
p. 12, as Theorem 5.4.1 of Bergh–Löfström): for `θ ∈ (0,1)`,
`(ℓ²(w₀), ℓ²(w₁))_{θ,2} = ℓ²(w₀^{1−θ} w₁^θ)` with equivalent norms, the constants depending only
on `θ`. -/
theorem stein_weiss_weighted_l2 (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (w₀ w₁ : ℕ → ℝ), (∀ ℓ, 0 < w₀ ℓ) → (∀ ℓ, 0 < w₁ ℓ) → ∀ a : ℕ → ℝ,
        ENNReal.ofReal c₁ * seqNormSq (fun ℓ => w₀ ℓ ^ (1 - θ) * w₁ ℓ ^ θ) a ≤
          seqInterpNormSq w₀ w₁ θ a ∧
        seqInterpNormSq w₀ w₁ θ a ≤
          ENNReal.ofReal c₂ * seqNormSq (fun ℓ => w₀ ℓ ^ (1 - θ) * w₁ ℓ ^ θ) a := by sorry

end SphereGRF.Spectral
