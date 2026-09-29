-- Prove2me | Theorems.Thm_TamingMonster_CoordDescent_halt_output_solves_OP
-- name    : TamingMonster.CoordDescent.halt_output_solves_OP
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:19:56.971903+00:00
-- url     : https://prove2.me/theorems/8c403f86-dc0f-47bc-afc8-88f69439601d
-- title:
--   Lemma 5 — if Algorithm 2 halts, its output solves (OP)
-- statement:
--   Let $K\ge1$ actions, a finite nonempty policy class $\Pi$, a history $H_t$ with $t\ge1$ records, and a minimum probability $0<\mu\le 1/(2K)$ be given, and let $b_\pi$, $D_\pi$ and the rescaling of Steps 4–6 of Algorithm 2 be as defined for these data.
--
--   Suppose the loop of Algorithm 2 is entered with nonnegative weights $Q_0$, Steps 4–6 produce $Q=\operatorname{rescale}(Q_0)$, and the algorithm halts at Step 10, i.e. $D_\pi(Q)\le0$ for every $\pi\in\Pi$. Then $Q$ solves (OP):
--   $$Q\ge0,\qquad \sum_{\pi\in\Pi}Q(\pi)\le1,\qquad \sum_{\pi\in\Pi}Q(\pi)b_\pi\le2K,\qquad \widehat{\mathbb E}_{x\sim H_t}\Bigl[\frac1{Q^\mu(\pi(x)\mid x)}\Bigr]\le2K+b_\pi\ \ \forall\pi\in\Pi .$$
--
--   This is the correctness half of Theorem 3: whenever Algorithm 2 stops, what it outputs is feasible for (OP).
--
--   **Formalization Note** The paper's "if Algorithm 2 halts and outputs a weight vector $Q$" is encoded as: $Q$ is the rescaling of a nonnegative weight vector $Q_0$ (every weight vector Algorithm 2 enters its loop with from $Q_{\mathrm{init}}\in\Delta^\Pi$ is nonnegative) and the Step-7 test fails for $Q$. The range $0<\mu\le1/(2K)$ is that of $\mu_m$ in Algorithm 1; $t\ge1$ makes $\widehat{\mathbb E}$ an average.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 10, Lemma 5 (proof App. D.1, p. 22)

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm

namespace TamingMonster.CoordDescent

/-- Lemma 5 (p. 10; proof App. D.1): if Algorithm 2 halts and outputs a weight vector `Q` —
i.e. the loop is entered with nonnegative weights `Q₀`, Steps 4–6 produce `Q = rescale Q₀`, and
no policy has `D_π(Q) > 0` (Step 7 fails and Step 10 halts) — then `Q` satisfies Eq. (3) and
Eq. (2), is nonnegative, and its weights sum to at most 1; that is, `Q` solves (OP). -/
theorem halt_output_solves_OP {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ)))
    (Q₀ : Pi → ℝ) (hQ₀ : ∀ π, 0 ≤ Q₀ π)
    (hhalt : HaltsAt Pi H μ Q₀) :
    SolvesOP Pi H μ (rescale Pi H μ Q₀) := by sorry

end TamingMonster.CoordDescent
