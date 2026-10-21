-- Prove2me | Theorems.Thm_StableFees_UserGain_expected_spacing_tendsto_zero
-- name    : StableFees.UserGain.expected_spacing_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:35.759342+00:00
-- url     : https://prove2.me/theorems/8e21d1c3-e62c-4939-bac1-d7e9263aeae4
-- title:
--   Proof of Result 3, p. 22 — expected adjacent spacing tends to zero
-- statement:
--   Fix $K\ge2$ and a continuous density $g$ of total mass one on $[0,\bar V]$, bounded below there by $\epsilon>0$. For $m$ i.i.d. draws $X_1,\ldots,X_m$ from this law, the adjacent top order statistic spacing is integrable whenever $m\ge K$, and
--
--   $$\lim_{m\to\infty}\mathbb E[V_{K-1}(X)-V_K(X)]=0.$$
--
--   This is the asymptotic input to the expected gain bound, with $m$ denoting the number of other active users.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 22, proof of Result 3; also p. 16, discussion preceding Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model
open MeasureTheory Filter

namespace StableFees.UserGain

theorem expected_spacing_tendsto_zero (K : ℕ) (hK : 2 ≤ K)
    (Vbar : ℝ) (g : ℝ → ℝ) (ε : ℝ) (hg : ValueDensity Vbar g ε) :
    (∀ m : ℕ, K ≤ m →
      Integrable (fun x : Fin m → ℝ => kthHighest x (K - 1) - kthHighest x K)
        (Measure.pi fun _ : Fin m => valueLaw Vbar g)) ∧
    Filter.Tendsto
      (fun m : ℕ => ∫ x : Fin m → ℝ, (kthHighest x (K - 1) - kthHighest x K)
        ∂(Measure.pi fun _ : Fin m => valueLaw Vbar g))
      Filter.atTop (nhds (0 : ℝ)) := by sorry

end StableFees.UserGain
