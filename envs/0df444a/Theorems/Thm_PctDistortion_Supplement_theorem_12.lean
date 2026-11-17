-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_12
-- name    : PctDistortion.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:34:14.640694+00:00
-- url     : https://prove2.me/theorems/11fd7aff-ce56-46f8-842f-ac6561e1d32d
-- title:
--   Theorem 12 — ABC$^{1/2}$-maximal lotteries have total-cost distortion at most $4-\nu(\mathcal G^{ABC}_{G^{1/2}_{\mathcal E}})$
-- statement:
--   For every election $\mathcal E=(V,\mathcal C,\vec\succ)$ and every equilibrium strategy $p\in\mathrm{ABC}^{1/2}(\mathcal E)$, the total-cost distortion of $p$ satisfies
--   $$\mathrm{dist}^+_{\mathcal E}(p)\le 4-\nu\big(\mathcal G^{ABC}_{G^{1/2}_{\mathcal E}}\big),$$
--   where $\nu(\mathcal G^{ABC}_{G^{1/2}_{\mathcal E}})$ is the value of the ABC game on the $1/2$-majority digraph of $\mathcal E$. In particular ABC$^{1/2}$-Maximal Lotteries has total-cost distortion at most this value.
--
--   This mirrors Theorem 1 for the total-cost objective; with Proposition 3 it gives the bound $4-1/m$ (Corollary 6), slightly below the bound $4$ known for C1-Maximal Lotteries.
--
--   Differences from the source:
--   - encoding: ABC^{1/2}-Maximal Lotteries has total-cost distortion at most 4 − ν; more precisely every p ∈ ABC^{1/2}(E) → ∀ p ∈ abcAlphaMaximal (1/2) E, totalDistortion E p ≤ ENNReal.ofReal (4 − abcValue (alphaMajority (1/2) E)); reason: the 'more precisely' sentence, which implies the rule form for every choice; totalDistortion is ℝ≥0∞-valued with the published distortion's ratio convention
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 12, p.32 (App. C)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_abcMaximal
import Definitions.Def_PctDistortion_Supplement_totalDistortion

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 12** (total cost). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 12, p.32 (App. C): "For every election
E = (V, C, ≻⃗), ABC^{1/2}-Maximal Lotteries has total-cost distortion at most
4 − ν(𝒢^ABC_{G^{1/2}_E}). More precisely, for every equilibrium strategy p ∈ ABC^{1/2}(E), the
expected total-cost distortion of p is at most 4 − ν(𝒢^ABC_{G^{1/2}_E})."

**Formalization Note.** Stated in the "more precisely" form, for every `p ∈ ABC^{1/2}(E)`
(published `abcAlphaMaximal (1/2) E`), which gives the rule form for every choice. `ν` is the
published `abcValue` of the ABC game on the 1/2-majority digraph `alphaMajority (1/2) E`. The
total-cost distortion is `totalDistortion`, `ℝ≥0∞`-valued with the published distortion's ratio
convention. -/
theorem theorem_12 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (E : Election V C) :
    ∀ p ∈ abcAlphaMaximal (1 / 2) E,
      totalDistortion E p ≤ ENNReal.ofReal (4 - abcValue (alphaMajority (1 / 2) E)) := by sorry

end PctDistortion.Supplement
