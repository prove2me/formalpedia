-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_taylor_display
-- name    : UniformDRO.LowerBound.taylor_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:41.174104+00:00
-- url     : https://prove2.me/theorems/c3521867-7714-4db9-93a1-e42bdaa815cf
-- title:
--   Proof of Thm 3 (App. D.1), p. 46 — c_k(p_k − δ)^{1/k*} ≤ c_k(c_k^{−1} − (1/k*) c_k^{k*/k} δ) = 1 − (1/k*) c_k^{k*} δ
-- statement:
--   Let $k > 1$, $\rho > 0$, $k_* = k/(k-1)$, $c_k = (1 + k(k-1)\rho)^{1/k}$ and $p_k = c_k^{-k_*}$. For $0 < \delta \le p_k$,
--   $$c_k (p_k - \delta)^{1/k_*} \le c_k\Bigl(c_k^{-1} - \frac{1}{k_*} c_k^{k_*/k}\,\delta\Bigr) = 1 - \frac{1}{k_*} c_k^{k_*}\,\delta .$$
--
--   Combined with the second claim of Lemma 12, this shows that the laws on $\{0, M\}$ with masses $p_k + \delta$ and $p_k - \delta$ at $M$ have robust risks separated by at least $(c_k^{k_*}/k_*) M\delta$, the separation used in the $n^{-1/2}$ branch of Theorem 3.
--
--   **Formalization Note.** Stated as two conjuncts, the inequality and the identity. The range $\delta \le p_k$ is the standing range $0 < \delta \le p_k \wedge (1 - p_k)$ of p. 45 (where $p_k - \delta \ge 0$ is the mass of a law). Real powers are `Real.rpow`.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 3 (App. D.1), p. 46, first display (Taylor's theorem)

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem taylor_display (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ ≤ pk k ρ) :
    UniformDRO.Concentration.ck k ρ * (pk k ρ - δ) ^ (1 / UniformDRO.Concentration.kstar k) ≤
        UniformDRO.Concentration.ck k ρ * (UniformDRO.Concentration.ck k ρ ^ (-1 : ℝ) - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ (UniformDRO.Concentration.kstar k / k) * δ) ∧
      UniformDRO.Concentration.ck k ρ * (UniformDRO.Concentration.ck k ρ ^ (-1 : ℝ) - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ (UniformDRO.Concentration.kstar k / k) * δ) =
        1 - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ UniformDRO.Concentration.kstar k * δ := by sorry

end UniformDRO.LowerBound
