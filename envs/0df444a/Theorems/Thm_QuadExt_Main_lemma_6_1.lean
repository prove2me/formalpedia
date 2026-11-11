-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_6_1
-- name    : QuadExt.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:04:31.36701+00:00
-- url     : https://prove2.me/theorems/c0f019dd-e00e-4c2f-8f53-a71fedd23c51
-- title:
--   Lemma 6.1 — a strong linear seeded extractor extracts from a high-derivative-entropy quadratic source with a correlated seed
-- statement:
--   Let $X = f(Y, Z)$ with $f$ quadratic, $Y = U_s$, $Z \in \mathbb F_2^t$ independent of $Y$, and
--   $f(Y, Z) = f_1(Y) + f_2(Y, Z) + f_3(Z)$ with $f_2$ bilinear and $H_\infty(\partial_a f_1(Y)) \ge k$ for all $a \ne 0$. Let $\mathrm{LExt} : \mathbb F_2^n \times \mathbb F_2^d \to \mathbb F_2^m$ be a $(k, \varepsilon)$-strong linear seeded extractor, and let $W$ be a random variable, correlated with $Z$ and independent of $Y$, with $W \approx_\delta U_d$. Put $B = 2^{-s} + 2\varepsilon + \delta$. Then with probability at least $1 - 2^m B^{1/2}$ over $(z, w) \sim (Z, W)$,
--   $$d_{TV}\big(\mathrm{LExt}(f(Y, z), w), U_m\big) \le 2^{m/2} B^{1/4}.$$
--   Furthermore, the same holds when $W \approx_\delta U_d$ is replaced by $H^\delta_\infty(W) \ge d - \Delta$, with $2\varepsilon + \delta$ replaced by $2^{\Delta+1}\varepsilon + \delta$ in both bounds. The lemma is the extraction step behind the quadratic correlation breaker (Lemma 7.3).
--
--   Differences from the source:
--   - encoding: $Z$ and the correlated seed $W$ → one joint distribution $\mu$ of $(Z, W)$ on $\mathbb F_2^t \times \mathbb F_2^d$, with $Y$ uniform and independent of it; reason: the most general $(Z, W)$ independent of $Y$.
--   - encoding: $\varepsilon \ge 0$ assumed; reason: $\varepsilon$ is an error parameter, and for $\varepsilon < 0$ the quantities $B^{1/2}$, $B^{1/4}$ can have a negative base and are undefined in the source.
--   - encoding: "with probability $1 - p$" → probability at least $1 - p$; $\Delta$ any real number; reason: standard reading; no constraint on $\Delta$ is stated.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 19 (PDF 20), Lemma 6.1

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_SeededExt

namespace QuadExt.Main

/-- **Lemma 6.1** (p. 19): for `X = f(Y, Z) = f₁(Y) + f₂(Y, Z) + f₃(Z)` with `f` quadratic,
`Y = U_s` independent of `(Z, W)`, `f₂` bilinear, `H_∞(∂_a f₁(Y)) ≥ k` for all `a ≠ 0`, a
`(k, ε)`-strong linear seeded extractor `LExt` and a seed `W ≈_δ U_d` (jointly distributed with
`Z` as `μ`): with probability at least `1 − 2^m (2^{−s} + 2ε + δ)^{1/2}` over `(z, w) ∼ μ`,
`d_TV(LExt(f(Y, z), w), U_m) ≤ 2^{m/2} (2^{−s} + 2ε + δ)^{1/4}`; and the same with
`H^δ_∞(W) ≥ d − Δ` in place of `W ≈_δ U_d` and `2^{Δ+1}ε + δ` in place of `2ε + δ`. -/
theorem lemma_6_1 (n s t d m : ℕ) (k ε δ : ℝ) (hε : 0 ≤ ε)
    (f : (Fin s ⊕ Fin t → ZMod 2) → (Fin n → ZMod 2)) (hf : IsQuadraticMap f)
    (f₁ : (Fin s → ZMod 2) → (Fin n → ZMod 2))
    (f₂ : (Fin s → ZMod 2) → (Fin t → ZMod 2) → (Fin n → ZMod 2))
    (f₃ : (Fin t → ZMod 2) → (Fin n → ZMod 2))
    (hdec : ∀ y w, f (join y w) = f₁ y + f₂ y w + f₃ w) (hf₂ : IsBilinear f₂)
    (hderiv : ∀ a : Fin s → ZMod 2, a ≠ 0 → k ≤ SSNonExt.minEntropy (source (dirDeriv a f₁)))
    (LExt : (Fin n → ZMod 2) → (Fin d → ZMod 2) → (Fin m → ZMod 2)) (hLExt : IsSLSE k ε ε LExt)
    (μ : PMF ((Fin t → ZMod 2) × (Fin d → ZMod 2))) :
    (SSNonExt.TV (μ.map Prod.snd) (PMF.uniformOfFintype (Fin d → ZMod 2)) ≤ δ →
      1 - (2 : ℝ) ^ (m : ℝ) * ((2 : ℝ) ^ (-(s : ℝ)) + 2 * ε + δ) ^ (1 / 2 : ℝ) ≤
        prob μ fun zw =>
          SSNonExt.TV ((unif (Fin s)).map fun y => LExt (f (join y zw.1)) zw.2)
              (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤
            (2 : ℝ) ^ ((m : ℝ) / 2) * ((2 : ℝ) ^ (-(s : ℝ)) + 2 * ε + δ) ^ (1 / 4 : ℝ)) ∧
    ∀ Δ : ℝ, SmoothMinEntropyGE δ (μ.map Prod.snd) ((d : ℝ) - Δ) →
      1 - (2 : ℝ) ^ (m : ℝ) *
          ((2 : ℝ) ^ (-(s : ℝ)) + (2 : ℝ) ^ (Δ + 1) * ε + δ) ^ (1 / 2 : ℝ) ≤
        prob μ fun zw =>
          SSNonExt.TV ((unif (Fin s)).map fun y => LExt (f (join y zw.1)) zw.2)
              (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤
            (2 : ℝ) ^ ((m : ℝ) / 2) *
              ((2 : ℝ) ^ (-(s : ℝ)) + (2 : ℝ) ^ (Δ + 1) * ε + δ) ^ (1 / 4 : ℝ) := by sorry

end QuadExt.Main
