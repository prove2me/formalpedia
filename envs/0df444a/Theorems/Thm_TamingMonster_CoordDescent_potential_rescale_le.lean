-- Prove2me | Theorems.Thm_TamingMonster_CoordDescent_potential_rescale_le
-- name    : TamingMonster.CoordDescent.potential_rescale_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:23:45.683831+00:00
-- url     : https://prove2.me/theorems/34aa5f9b-45d1-47f2-b6e4-2dba5723d537
-- title:
--   Lemma 6 — the rescaling step does not increase the potential: $\Phi_m(cQ)\le\Phi_m(Q)$
-- statement:
--   Let $K\ge1$, a finite nonempty policy class $\Pi$, a history $H_t$ with $t\ge1$ records, and $0<\mu\le1/(2K)$ be given, with $b_\pi$ and the potential $\Phi_m$ of Eq. (6) defined from them ($\tau=t$).
--
--   Let $Q$ be a nonnegative weight vector on $\Pi$ with $\sum_\pi Q(\pi)(2K+b_\pi)>2K$, and let $c=2K/\sum_\pi Q(\pi)(2K+b_\pi)$ as in Eq. (4). Then
--   $$\Phi_m(cQ)\le\Phi_m(Q).$$
--
--   Together with Lemma 7 this shows that Algorithm 2 makes monotone progress on $\Phi_m$: the rescaling of Steps 4–5 never increases it.
--
--   **Formalization Note** The paper's "weight vector" is taken as a nonnegative vector without a bound on its sum, since Algorithm 2 applies Step 5 to vectors whose weights may sum to more than 1 after Step 8. The range $0<\mu\le1/(2K)$ is that of $\mu_m$ in Algorithm 1.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 10, Lemma 6 (proof App. D.2, pp. 22-23)

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm
import Definitions.Def_TamingMonster_CoordDescent_Potential

namespace TamingMonster.CoordDescent

/-- Lemma 6 (p. 10; proof App. D.2): let `Q` be a (nonnegative) weight vector with
`∑_π Q(π)(2K + b_π) > 2K`, and let `c = 2K / ∑_π Q(π)(2K + b_π)` as in Eq. (4). Then
`Φ(cQ) ≤ Φ(Q)`. -/
theorem potential_rescale_le {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q : Pi → ℝ) (hQ : ∀ π, 0 ≤ Q π)
    (hmass : 2 * (K : ℝ) < weightedMass Pi H μ Q) :
    potential Pi H μ (fun π => scaleFactor Pi H μ Q * Q π) ≤ potential Pi H μ Q := by sorry

end TamingMonster.CoordDescent
