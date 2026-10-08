-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_delta_stein_eq
-- name    : PoissonDepTrials.MixInv.delta_stein_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:51.807216+00:00
-- url     : https://prove2.me/theorems/197dbeba-202f-49ba-bf24-c79230bca0cd
-- title:
--   (3.6), p. 537 — ΔS_λh(w) = −λ^{−1}[h(w) − 𝒫_λh − (w − λ)S_λh(w)]
-- statement:
--   Let $\lambda>0$ and $h$ bounded. For every $w\ge1$,
--   $$\Delta S_\lambda h(w)=-\lambda^{-1}\bigl[h(w)-\mathcal P_\lambda h-(w-\lambda)S_\lambda h(w)\bigr].$$
--   This rearrangement of Stein's equation (2.3) is the identity from which Lemma 3.5 follows.
--
--   **Formalization Note** $\lambda>0$ and boundedness of $h$ (a bound $M$) are the standing assumptions of §3 and are stated.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, proof of Lemmas 3.4 and 3.5, (3.6)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem delta_stein_eq (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → delta (stein lam h) w =
      -lam⁻¹ * (h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w) := by sorry

end PoissonDepTrials.MixInv
