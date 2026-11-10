-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_8
-- name    : QPSpinProfile.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:45.59035+00:00
-- url     : https://prove2.me/theorems/528d7e62-2e7c-4373-b80e-da8a7ef3f088
-- title:
--   Lemma 2.8: product-state energy benchmark
-- statement:
--   There is a universal constant $C<\infty$ such that for every $n\ge p\ge2$,
--   $$
--   \mathbb E\,E_{n,p}(\mathrm{prod}_n)\le C\sqrt{n\log(ep)},
--   $$
--   and for every $t>0$,
--   $$
--   \mathbb P\Big(E_{n,p}(\mathrm{prod}_n)>C\sqrt{n\log(ep)}+t\Big)\le\exp(-t^2/2).
--   $$
--   Both bounds hold with the same constant $C$.
--
--   The product-state optimum is thus of order $\sqrt{n\log p}$, much smaller than the ground-state scale $3^{p/2}\sqrt n/p$ for large $p$.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: $\mathbb E\,E_{n,p}(\mathrm{prod}_n)$, a finite number → Bochner integral, with integrability of $E_{n,p}(\mathrm{prod}_n)$ asserted as a conclusion; reason: the variable can be negative, so a lower Lebesgue integral would be wrong; asserting integrability excludes the junk value $0$
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.8, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_QPSpinProfile_prodStatesOn
import Definitions.Def_QPSpinProfile_maxEnergy

namespace QPSpinProfile

open MeasureTheory

/-- **Lemma 2.8 (Product-state energy benchmark)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.26, PDF p.29).
There is a universal constant `C` such that for every `n ≥ p ≥ 2`,
`E E_{n,p}(prod_n) ≤ C √(n log(ep))`, and for every `t > 0`,
`P(E_{n,p}(prod_n) > C √(n log(ep)) + t) ≤ exp(−t²/2)`. Both clauses share one `C`.

**Formalization Note** `E_{n,p}(prod_n)` can be negative, so its expectation is a Bochner integral
and the statement also asserts its integrability. -/
theorem lemma_2_8 : ∃ C : ℝ, 0 < C ∧
    ∀ (n p : ℕ), 2 ≤ p → p ≤ n →
      Integrable (maxEnergy n p (prodStates n)) (gaussMeasure n p) ∧
      ∫ g, maxEnergy n p (prodStates n) g ∂(gaussMeasure n p)
        ≤ C * Real.sqrt (n * Real.log (Real.exp 1 * p)) ∧
      ∀ t : ℝ, 0 < t →
        gaussMeasure n p
            {g | C * Real.sqrt (n * Real.log (Real.exp 1 * p)) + t < maxEnergy n p (prodStates n) g}
          ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by sorry

end QPSpinProfile
