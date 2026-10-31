-- Prove2me | Theorems.Thm_PlugInRisk_corollary_3_5
-- name    : PlugInRisk.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:02.793951+00:00
-- url     : https://prove2.me/theorems/86860497-8299-4abf-9a44-c01701600d63
-- title:
--   Corollary 3.5: sup-norm covering numbers of $\{f(F+g\cdot G-m)\}$
-- statement:
--   Let $m_0\in\mathbb R$, let $f:\mathbb R\to\mathbb R$ be locally Lipschitz, let $F,G_1,\dots,G_e$ be measurable with $J=1+|F|+\sum_i|G_i|$ bounded, and let $\mathcal G\subset\mathbb R^e$ be countable and bounded. Then there is $C>0$ such that
--
--   $$
--   \mathcal N\Bigl(\bigl\{f(F+g\cdot G-m):g\in\mathcal G,\ m\in[-m_0,m_0]\bigr\},\ \|\cdot\|_\infty,\ \varepsilon\Bigr)\le\Bigl(\frac{C}{\varepsilon}\Bigr)^{e+1}\vee1\qquad\text{for every }\varepsilon>0,
--   $$
--
--   where $\|\cdot\|_\infty$ is the supremum norm (not the essential supremum).
--
--   Differences from the source:
--
--   - reading: C generic → C chosen after 𝒳, F, G, 𝒢, m₀, f and before ε; reason: the paper's convention for constants (p.11)
--   - encoding: N(·, ‖·‖_∞, ε) → internal coveringNumber in ℕ∞ for the [0, ∞]-valued distance sup_x |h x − h' x|; reason: the paper's covering numbers (p.11) and supremum norm (footnote 7)
--   - encoding: 𝒢 countable and bounded (standing, p.11); 𝒳 Polish (p.6) → explicit hypotheses; reason: standing assumptions of the paper
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Corollary 3.5, p.15

import Mathlib
import Definitions.Def_PlugInRisk_coveringNumber

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Corollary 3.5** (Bartl & Tangpi, arXiv:2003.10479v2, Corollary 3.5, p.15): "Let m₀ ∈ ℝ, let
f : ℝ → ℝ be locally Lipschitz continuous, and assume that J is bounded. Then it holds that
N( {f(F + g·G − m) : g ∈ 𝒢 and m ∈ [−m₀, m₀]}, ‖·‖_∞, ε ) ≤ (C/ε)^{e+1} ∨ 1 for every
ε > 0."

Here `J := 1 + |F| + Σᵢ|Gᵢ|`, `‖·‖_∞` is the supremum norm over `𝒳` (footnote 7, p.15), and
`𝒢 ⊂ ℝᵉ` is countable and bounded (standing assumption, p.11).

**Formalization Note** The covering number is internal (`coveringNumber`, p.11) for the
`[0, ∞]`-valued supremum distance `sup_x |h x − h' x|`. `C` is chosen after the data
`𝒳, F, G, 𝒢, m₀, f` and before `ε` (the paper's convention for generic constants, p.11). -/
theorem corollary_3_5 {e : ℕ}
    (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (F : 𝒳 → ℝ) (hF : Measurable F) (G : Fin e → 𝒳 → ℝ) (hG : ∀ i, Measurable (G i))
    (𝒢 : Set (Fin e → ℝ)) (h𝒢c : 𝒢.Countable) (h𝒢b : Bornology.IsBounded 𝒢)
    (m₀ : ℝ) (f : ℝ → ℝ) (hf : LocallyLipschitz f)
    (hJ : ∃ K : ℝ, ∀ x, 1 + |F x| + ∑ i, |G i x| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      (coveringNumber (fun h h' : 𝒳 → ℝ => ⨆ x, edist (h x) (h' x))
          {h | ∃ g ∈ 𝒢, ∃ m ∈ Set.Icc (-m₀) m₀, h = fun x => f (F x + ∑ i, g i * G i x - m)}
          (ENNReal.ofReal ε) : ℝ≥0∞)
        ≤ ENNReal.ofReal (max ((C / ε) ^ (e + 1)) 1) := by sorry

end PlugInRisk
