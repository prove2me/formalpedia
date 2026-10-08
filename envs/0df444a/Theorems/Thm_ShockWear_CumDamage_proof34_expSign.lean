-- Prove2me | Theorems.Thm_ShockWear_CumDamage_proof34_expSign
-- name    : ShockWear.CumDamage.proof34_expSign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:11.977748+00:00
-- url     : https://prove2.me/theorems/0288eac2-5303-4411-b7d4-e9cbce44bb23
-- title:
--   Proof of (3.4), p. 633 — for every $\theta > 0$, $\bar H(t) - e^{-\theta t}$ has at most one sign change, $+$ to $-$
-- statement:
--   Let $\lambda > 0$, let $1 = \bar P_0 \ge \bar P_1 \ge \dots \ge 0$ with $\bar P_k^{1/k}$ decreasing in $k = 1, 2, \dots$, and let $\bar H$ be the shock survival function (2.1). Then for every $\theta > 0$, the function
--   $$t \mapsto \bar H(t) - e^{-\theta t}, \qquad t \ge 0,$$
--   has at most one sign change, from $+$ to $-$ if one occurs.
--
--   This is the third step of the paper's proof of Theorem 3.1 (3.4), obtained from the previous step and (2.6); it is the sign change characterization of the IHRA property.
--
--   **Formalization Note** The property is stated on $t \ge 0$: for $t < 0$, $\bar H(t) = 1 < e^{-\theta t}$. $\bar P_k \ge 0$ is stated explicitly; $\bar P_k^{1/k}$ is a real power.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 633, proof of (3.4), third sentence

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem proof34_expSign (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    ∀ θ : ℝ, 0 < θ → SignPM (fun t => shockSurv lam P t - Real.exp (-(θ * t))) (Set.Ici 0) := by sorry

end ShockWear.CumDamage
