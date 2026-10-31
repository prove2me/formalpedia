-- Prove2me | Theorems.Thm_TabooRegen_uniform_key_renewal
-- name    : TabooRegen.uniform_key_renewal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:42.985682+00:00
-- url     : https://prove2.me/theorems/ecfe12f3-f9a3-4cc5-b8bc-254a728d2e98
-- title:
--   Reference [1] (Arjas–Nummelin–Tweedie) — uniform key renewal theorem for spread-out laws
-- statement:
--   Let $F$ be a spread-out probability measure on $[0,\infty)$ with finite mean $m$, let $U=\sum_{n\ge0}F^{*n}$ be its renewal measure, and let $h$ be non-increasing and integrable on $[0,\infty)$. Then
--
--   $$
--   \sup\Big\{\Big|\int_{[0,t]}b(t-s)\,U(ds)-\frac1m\int_0^\infty b(s)\,ds\Big|:\ b\text{ measurable},\ |b(s)|\le h(s)\text{ for }s\ge0\Big\}\longrightarrow0\qquad(t\to\infty).
--   $$
--
--   This is the uniform version of Smith's key renewal theorem that the paper invokes (citing Arjas, Nummelin and Tweedie, 1978) to make the convergence of (4.2) uniform over the sets $B$ and the window widths $\ell$.
--
--   Differences from the source:
--   - encoding: spread-out $F$, renewal measure $\sum_n F^{*n}$, mean $m$ → `InClassS F`, `renewalMeasure δ₀ F`, `mean F` of the referenced renewal definitions; reason: the same objects
--   - encoding: $\sup\{|\cdots|:b\text{ measurable},\ |b|\le h\}\to0$ → for every $\varepsilon>0$, eventually in $t$, $|\cdots|\le\varepsilon$ for every measurable $b$ with $|b|\le h$ on $[0,\infty)$; reason: equivalent, since a supremum tends to $0$ exactly when it is eventually at most every $\varepsilon$
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, reference [1] (E. Arjas, E. Nummelin and R.L. Tweedie, Uniform limit theorems for non-singular renewal and Markov renewal processes, J. Appl. Probab. 15 (1978) 112–125), invoked on p.281 and in the proof of Theorem 2, p.287 (PDF p.17)

import Mathlib
import Definitions.Def_TabooRegen_Window

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open Model

/-- **The uniform key renewal theorem for spread-out laws** (Arjas, Nummelin and Tweedie 1978,
reference [1] of Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004), invoked on p.281 and in the proof of Theorem 2, p.287: "the renewal theorem
guarantees uniform convergence (over `B`, `ℓ`) of the convolution of `b̃B,ℓ` with `Σ0^∞ G̃(ℓ)`").
Let `F` be a spread-out probability measure on `[0, ∞)` with finite mean `m`, and let `h` be
non-increasing and integrable on `[0, ∞)`. Then, with `U = Σ_{n ⩾ 0} F^{*n}`,
`sup {|∫_{[0,t]} b(t − s) U(ds) − m⁻¹ ∫₀^∞ b(s) ds| : b measurable, |b| ⩽ h on [0, ∞)} → 0`
as `t → ∞`.

**Formalization Note.** `F^{*n}` and `U` are `convPow` and `renewalMeasure δ₀ F`, spread-out is
`InClassS`, and `m` is `mean F`, all from the referenced `SmithRegenerative.Equilibrium`
definitions. `sup … → 0` is written `∀ ε > 0`, eventually in `t`, for every dominated `b`. -/
theorem uniform_key_renewal (F : Measure ℝ) [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0)
    (hS : SmithRegenerative.Equilibrium.InClassS F)
    (hm : SmithRegenerative.Equilibrium.mean F < ⊤) (h : ℝ → ℝ)
    (hh : AntitoneOn h (Set.Ici 0)) (hhi : IntegrableOn h (Set.Ici 0)) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ b : ℝ → ℝ, Measurable b → (∀ s, 0 ≤ s → |b s| ≤ h s) →
      |∫ s in Set.Icc 0 t, b (t - s)
          ∂(SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) F) -
        (SmithRegenerative.Equilibrium.mean F).toReal⁻¹ * ∫ s in Set.Ioi 0, b s| ≤ ε := by sorry

end TabooRegen
