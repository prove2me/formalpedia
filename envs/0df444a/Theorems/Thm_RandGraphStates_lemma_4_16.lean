-- Prove2me | Theorems.Thm_RandGraphStates_lemma_4_16
-- name    : RandGraphStates.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:35.603848+00:00
-- url     : https://prove2.me/theorems/25fbe224-ee56-4361-9a53-54e045122eed
-- title:
--   Lemma 4.16: bulk nullity tail
-- statement:
--   Suppose $t\to\infty$, $\log m=o(t^2)$ and
--   $$
--   \frac{p_-^2m}{\log(e/p_-)}\gg t+\log m .
--   $$
--   Then
--   $$
--   \pi^p_m(t)\le2^{-\binom t2+O(t+\log m)}=2^{-\binom t2+o(t^2)}.
--   $$
--   This is the tail used for the large submatrices in the union bound of Theorem 4.17.
--
--   Differences from the source:
--   - encoding: t → ∞, log m = o(t²), ≫, O(·), o(·) → arbitrary sequences (m_i, t_i, p_i) with Tendsto and =o hypotheses; ≫ as the ratio tending to ∞; ∃ C before the sequences; both forms of the bound eventually; o(t²) as every ε > 0; reason: the asymptotics of the printed statement, with an absolute O-constant
--   - encoding: unsubscripted log → natural logarithm; reason: the base changes only the O-constant and no hypothesis here
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Lemma 4.16, p.30

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Lemma 4.16** (bulk nullity tail). If `t → ∞`, `log m = o(t²)` and
`p₋² m / log(e/p₋) ≫ t + log m`, then `π^p_m(t) ≤ 2^{-C(t,2)+O(t+log m)} = 2^{-C(t,2)+o(t²)}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Lemma 4.16, p.30.

**Formalization Note.** The asymptotics run along arbitrary sequences `(m_i, t_i, p_i)`; `≫` means the ratio tends
to infinity. The `O`-constant is absolute: `∃ C` comes before the sequences. `log` is natural. -/
theorem lemma_4_16 :
    ∃ C : ℝ, ∀ (m t : ℕ → ℕ) (p : ℕ → ℝ), (∀ i, 0 < p i ∧ p i < 1) →
      Tendsto t atTop atTop →
      (fun i => Real.log (m i)) =o[atTop] (fun i => ((t i : ℝ)) ^ 2) →
      Tendsto (fun i => (pMinus (p i) ^ 2 * (m i : ℝ) / Real.log (Real.exp 1 / pMinus (p i))) /
        ((t i : ℝ) + Real.log (m i))) atTop atTop →
      (∀ᶠ i in atTop, piTail (p i) (m i) (t i) ≤
        (2 : ℝ) ^ (-(((t i).choose 2 : ℕ) : ℝ) + C * ((t i : ℝ) + Real.log (m i)))) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, piTail (p i) (m i) (t i) ≤
        (2 : ℝ) ^ (-(((t i).choose 2 : ℕ) : ℝ) + ε * (t i : ℝ) ^ 2)) := by sorry

end RandGraphStates
