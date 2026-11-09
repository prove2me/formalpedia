-- Prove2me | Theorems.Thm_PhiSobBayes_lemma_A_19
-- name    : PhiSobBayes.lemma_A_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:46.206068+00:00
-- url     : https://prove2.me/theorems/5f4d93c5-b999-4043-86a5-6edb1d3ccbb1
-- title:
--   Lemma A.19 — entropy decomposition of a mixture
-- statement:
--   Let $J$ be an interval, $\Phi:J\to\mathbb R$ convex, and $\pi=\int\pi_y\,\rho(dy)$ a mixture of probability measures $\pi_y$ over a probability measure $\rho$. Let $f$ be a $J$-valued function such that $f$ and $\Phi(f)$ are $\pi$-integrable, and let $H(y)=\mathbb E_{\pi_y}f$. Then
--   $$\mathrm{Ent}^\Phi_\pi(f)=\int\mathrm{Ent}^\Phi_{\pi_y}(f)\,\rho(dy)+\mathrm{Ent}^\Phi_\rho(H).\tag{77}$$
--
--   Applied to the mixture $\mu=\mathbb E_{y\sim Y_t}\mu_{t,y}$ of (46), it gives the second equality of the Bayes risk decomposition (47).
--
--   Differences from the source:
--   - encoding: a mixture π = ∫ π_y ρ(dy) of probability measures π_y → a Markov kernel κ (the measurable family y ↦ π_y) and π = ρ.bind κ; reason: a mixture needs y ↦ π_y measurable; a Markov kernel is exactly that
--   - encoding: unspecified spaces → arbitrary measurable spaces α (for f) and β (for y); reason: the paper does not fix the spaces; no space is excluded
--   - encoding: J an interval → Set.OrdConnected J; reason: the order-connected subsets of ℝ are exactly the intervals
--   - encoding: Φ : J → ℝ convex → Φ : ℝ → ℝ with ConvexOn ℝ J Φ; reason: Lean functions are total; f is J-valued, so Φ is only evaluated on J (up to a ρ-null set of y for Φ(H(y)))
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma A.19, p.60 (PDF 60), display (77)

import Mathlib
import Definitions.Def_PhiSobBayes_phiEnt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Lemma A.19 (entropy decomposition).** Let `J` be an interval, `Φ` convex on `J`, and
`π = ∫ π_y ρ(dy)` a mixture of probability measures `π_y` over a probability measure `ρ`. If `f` is
`J`-valued and `f`, `Φ(f)` are `π`-integrable, then with `H(y) = 𝔼_{π_y} f`,
`Ent^Φ_π(f) = ∫ Ent^Φ_{π_y}(f) ρ(dy) + Ent^Φ_ρ(H)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Lemma A.19, p.60 (PDF 60), display (77).

**Formalization Note** The measurable family `y ↦ π_y` is a Markov kernel `κ`, and the mixture is
`π = ρ.bind κ`. The spaces are arbitrary measurable spaces. "Interval" is `Set.OrdConnected`; `J`
need not be open and `Φ` need not be continuous. -/
theorem lemma_A_19 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (κ : Kernel β α) [IsMarkovKernel κ]
    (J : Set ℝ) (hJ : J.OrdConnected) (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ J Φ)
    (f : α → ℝ) (hfJ : ∀ x, f x ∈ J) (hf : Integrable f (ρ.bind κ))
    (hΦf : Integrable (fun x => Φ (f x)) (ρ.bind κ)) :
    phiEnt (ρ.bind κ) Φ f =
      ∫ y, phiEnt (κ y) Φ f ∂ρ + phiEnt ρ Φ (fun y => ∫ x, f x ∂(κ y)) := by sorry

end PhiSobBayes
