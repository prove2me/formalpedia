-- Prove2me | Theorems.Thm_PlugInRisk_lemma_3_4
-- name    : PlugInRisk.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:30.135863+00:00
-- url     : https://prove2.me/theorems/02b6c102-e579-4af7-a155-e13928d0eb20
-- title:
--   Lemma 3.4: the class $\{f(F+g\cdot G-m)+\kappa m\}$ satisfies Assumption A.3
-- statement:
--   Let $\mu$ be a probability law on a Polish space $\mathcal X$, $F,G_1,\dots,G_e$ measurable, $\mathcal G\subset\mathbb R^e$ countable, $m_0,\kappa\in\mathbb R$ and $f:\mathbb R\to\mathbb R$ continuous. Assume there is $D\in L^2(\mu)$ with $|f(F+g\cdot G-m)|\le D$ $\mu$-a.e. for all $g\in\mathcal G$, $m\in[-m_0,m_0]$. Then
--
--   $$
--   \mathcal H:=\bigl\{f(F+g\cdot G-m)+\kappa m:\ g\in\mathcal G,\ m\in[-m_0,m_0]\bigr\}
--   $$
--
--   consists of measurable $\mu$-square integrable functions and satisfies Assumption A.3.
--
--   The paper states this for $f=l$ a loss function and $\kappa=1$ (the class of Lemma 3.3), and uses it for $f=(\cdot)^+$, $\kappa=0$ in Theorem 5.1. It makes Dudley's bound and the deviation inequality applicable to these classes.
--
--   Differences from the source:
--
--   - generalization: ℋ = {l(F + g·G − m) + m} for a loss function l with l' of polynomial growth of degree p − 1, ‖F‖_{L^{2p}(μ)}, ‖G‖_{L^{2p}(μ)} < ∞, 𝒢 bounded (Theorem 3.1, Lemma 3.3) → any continuous f and κ ∈ ℝ, 𝒢 countable, with an a.e. bound |f(F + g·G − m)| ≤ D ∈ L²(μ); reason: under the source's hypotheses |l(y)| ≤ C(1 + |y|ᵖ) and |F + g·G − m| ≤ C₀J + |m₀| give D = C(1 + (C₀J + |m₀|)ᵖ) ∈ L²(μ) (a constant if p = ∞); κ = 1, f = l is the source's class
--   - encoding: ℋ satisfies Assumption A.3 (a set of measurable, μ-square integrable functions, p.34) → (∀ h ∈ ℋ, Measurable h ∧ MemLp h 2 μ) ∧ SatisfiesA3 μ ℋ; reason: the standing requirement of App. A.2 is part of the claim
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 3.4, p.15, with the class of Lemma 3.3, p.13

import Mathlib
import Definitions.Def_PlugInRisk_SatisfiesA3

open MeasureTheory

namespace PlugInRisk

/-- **Lemma 3.4** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 3.4, p.15): "The set ℋ defined in
Lemma 3.3 satisfies Assumption A.3", where (Lemma 3.3, p.13)
`ℋ := {l(F + g·G − m) + m : g ∈ 𝒢 and m ∈ [−m₀, m₀]}`.

Stated for an arbitrary continuous `f` in place of the loss function `l` and an arbitrary
coefficient `κ` in place of `1`: if `𝒢 ⊂ ℝᵉ` is countable, `F, Gᵢ` are measurable, and the
functions `f(F + g·G − m)`, `g ∈ 𝒢`, `|m| ≤ m₀`, are dominated `μ`-a.e. by one `D ∈ L²(μ)`, then
`ℋ = {f(F + g·G − m) + κm : g ∈ 𝒢, m ∈ [−m₀, m₀]}` is a set of measurable, `μ`-square
integrable functions (the standing requirement of App. A.2, p.34) satisfying Assumption A.3.

**Formalization Note** The paper's case is `f = l` a loss function with `l'` of polynomial
growth of degree `p − 1` and `‖F‖_{L^{2p}(μ)}, ‖G‖_{L^{2p}(μ)} < ∞` (Theorem 3.1, Lemma 3.3),
`𝒢` bounded, and `κ = 1`; there `|l(F + g·G − m)| ≤ C(1 + (C₀J + |m₀|)ᵖ) ∈ L²(μ)` (a constant
if `p = ∞`) supplies `D`. Theorem 5.1's proof (p.26) uses the case `f = (·)⁺`, `κ = 0`. -/
theorem lemma_3_4 {e : ℕ}
    (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : 𝒳 → ℝ) (hF : Measurable F) (G : Fin e → 𝒳 → ℝ) (hG : ∀ i, Measurable (G i))
    (𝒢 : Set (Fin e → ℝ)) (h𝒢c : 𝒢.Countable)
    (m₀ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (κ : ℝ)
    (D : 𝒳 → ℝ) (hD : MemLp D 2 μ)
    (hdom : ∀ᵐ x ∂μ, ∀ g ∈ 𝒢, ∀ m ∈ Set.Icc (-m₀) m₀,
      |f (F x + ∑ i, g i * G i x - m)| ≤ D x)
    (ℋ : Set (𝒳 → ℝ))
    (hℋ : ℋ = {h | ∃ g ∈ 𝒢, ∃ m ∈ Set.Icc (-m₀) m₀,
      h = fun x => f (F x + ∑ i, g i * G i x - m) + κ * m}) :
    (∀ h ∈ ℋ, Measurable h ∧ MemLp h 2 μ) ∧ SatisfiesA3 μ ℋ := by sorry

end PlugInRisk
