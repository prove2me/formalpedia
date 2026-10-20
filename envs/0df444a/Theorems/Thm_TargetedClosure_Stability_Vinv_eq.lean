-- Prove2me | Theorems.Thm_TargetedClosure_Stability_Vinv_eq
-- name    : TargetedClosure.Stability.Vinv_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:12.04945+00:00
-- url     : https://prove2.me/theorems/3035bca5-de92-4d22-a923-ff9a49e3123a
-- title:
--   Proof of Lemma 2.1 — inverse of V and nonnegative entries
-- statement:
--   In the spatial epidemic model, let $V$ be the transition Jacobian and $F(x)$ the new-infection Jacobian at the disease-free equilibrium. If the model assumptions hold and each activity level lies in $[0,1]$, then $V^{-1}$ has the three-block form displayed in the proof of Lemma 2.1, and
--
--   $$
--   (V^{-1})_{pq}\geq0,\qquad (F(x)V^{-1})_{pq}\geq0
--   $$
--
--   for every pair of infected coordinates $p,q$. The inverse identity connects the compartment transitions to the nonnegative next generation matrix used in condition (6).
--
--   **Formalization Note** The block order is exposed, clinical, subclinical. Positivity of $\mu+\kappa$ and $\mu+\gamma$ follows from the standing rate assumptions.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), p. 13 (PDF 14), paragraph before Lemma 2.1 and proof of Lemma 2.1

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem Vinv_eq {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    (Vmat P)⁻¹ = Vinv P ∧
    (∀ p q, 0 ≤ (Vmat P)⁻¹ p q) ∧
    (∀ p q, 0 ≤ (Fmat P x * (Vmat P)⁻¹) p q) := by sorry

end TargetedClosure.Stability
