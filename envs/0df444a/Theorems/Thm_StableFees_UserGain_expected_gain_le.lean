-- Prove2me | Theorems.Thm_StableFees_UserGain_expected_gain_le
-- name    : StableFees.UserGain.expected_gain_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:34.507485+00:00
-- url     : https://prove2.me/theorems/fdf6a3bf-fa18-494c-80d8-b8188eec89e6
-- title:
--   Proof of Result 3, p. 22 — expected gain is bounded by expected spacing
-- statement:
--   Let $2\le K\le m$, let $v\in[0,\bar V]$, and let the $m$ other active users bid their i.i.d. values from a continuous density $g$ on $[0,\bar V]$, with $g\ge\epsilon>0$ and total mass one. The payoff $u_K(v,b;X)$ of every admissible bid $b\in[0,\bar V]$ and the adjacent order statistic spacing are integrable, and the expected gain from strategic bidding (the best expected payoff over bids fixed before the others' bids are seen, less the expected truthful payoff) satisfies
--
--   $$\mathcal G_{K,\bar V}(v;m)=\sup_{b\in[0,\bar V]}\mathbb E[u_K(v,b;X)]-\mathbb E[u_K(v,v;X)]\le\mathbb E[V_{K-1}(X)-V_K(X)].$$
--
--   The right side does not depend on the considered bidder's value. Integrability is explicit so the expectation has its ordinary meaning.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 22, proof of Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model
open MeasureTheory

namespace StableFees.UserGain

theorem expected_gain_le (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar : ℝ) (g : ℝ → ℝ) (ε : ℝ) (hg : ValueDensity Vbar g ε)
    (v : ℝ) (hv : v ∈ Set.Icc 0 Vbar) :
    (∀ b ∈ Set.Icc 0 Vbar, Integrable (fun x : Fin m → ℝ => payoff K v b x)
      (Measure.pi fun _ : Fin m => valueLaw Vbar g)) ∧
    Integrable (fun x : Fin m → ℝ => kthHighest x (K - 1) - kthHighest x K)
      (Measure.pi fun _ : Fin m => valueLaw Vbar g) ∧
    expectedGain K Vbar (valueLaw Vbar g) m v ≤
      ∫ x, (kthHighest x (K - 1) - kthHighest x K)
        ∂(Measure.pi fun _ : Fin m => valueLaw Vbar g) := by sorry

end StableFees.UserGain
