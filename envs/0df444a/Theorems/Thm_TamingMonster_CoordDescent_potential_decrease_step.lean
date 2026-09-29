-- Prove2me | Theorems.Thm_TamingMonster_CoordDescent_potential_decrease_step
-- name    : TamingMonster.CoordDescent.potential_decrease_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:27:45.110981+00:00
-- url     : https://prove2.me/theorems/4d8eaefc-7b58-45ad-82ab-87bb2f0f08e6
-- title:
--   Lemma 7 — each coordinate step decreases the potential by at least $\tau\mu^2/(4(1-K\mu))$
-- statement:
--   Let $K\ge1$, a finite nonempty policy class $\Pi$, a history $H_\tau$ with $\tau\ge1$ records, and $0<\mu\le1/(2K)$ be given, with $b_\pi$, $V_\pi$, $S_\pi$, $D_\pi$, $\alpha_\pi$ (Algorithm 2) and $\Phi_m$ (Eq. (6)) defined from them.
--
--   Let $Q$ be a nonnegative set of weights on $\Pi$ and suppose that $D_\pi(Q)>0$ for some policy $\pi\in\Pi$. Let $Q'$ be the copy of $Q$ with $Q'(\pi)=Q(\pi)+\alpha$, where $\alpha=\alpha_\pi(Q)$. Then $\alpha>0$ and
--   $$\Phi_m(Q)-\Phi_m(Q')\ge\frac{\tau\mu^2}{4(1-K\mu)}\qquad(7).$$
--
--   Every execution of Step 8 of Algorithm 2 therefore lowers the potential by a fixed amount, which, with $\Phi_m\ge0$ and the value of $\Phi_m$ at $Q=\mathbf 0$, bounds the number of iterations in Theorem 3.
--
--   **Formalization Note** The paper states "$\alpha=\alpha_\pi(Q)>0$" as part of the lemma; the positivity is a conclusion here. The range $0<\mu\le1/(2K)$ is that of $\mu_m$ in Algorithm 1.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 10, Lemma 7, Eq. (7) (proof App. D.3, pp. 23-24)

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm
import Definitions.Def_TamingMonster_CoordDescent_Potential

namespace TamingMonster.CoordDescent

/-- Lemma 7 (p. 10; proof App. D.3): let `Q` be a (nonnegative) set of weights and suppose that
`D_π(Q) > 0` for some policy `π`. Let `Q'` be the copy of `Q` with `Q'(π) = Q(π) + α`, where
`α = α_π(Q)`. Then `α > 0` and, with `τ = t` the length of the history,
`Φ(Q) − Φ(Q') ≥ τμ² / (4(1 − Kμ))` (Eq. (7)). -/
theorem potential_decrease_step {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π) (π : Pi)
    (hD : 0 < Dfun Pi H μ Q π) :
    0 < alphaStep Pi H μ Q π ∧
      (t : ℝ) * μ ^ 2 / (4 * (1 - (K : ℝ) * μ))
        ≤ potential Pi H μ Q - potential Pi H μ (addAlpha Pi H μ Q π) := by sorry

end TamingMonster.CoordDescent
