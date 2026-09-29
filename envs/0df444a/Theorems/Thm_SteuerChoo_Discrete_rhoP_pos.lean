-- Prove2me | Theorems.Thm_SteuerChoo_Discrete_rhoP_pos
-- name    : SteuerChoo.Discrete.rhoP_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:46:58.292315+00:00
-- url     : https://prove2.me/theorems/844310b4-e859-4fab-a32e-1bd213828049
-- title:
--   Proof of Theorem 3.4 — the augmentation coefficient ρ_p of (3.6) is positive
-- statement:
--   Let $k \ge 1$, let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, and let $z^*$ be an ideal criterion vector for $Z$. For $z^p \in N$, the coefficient
--   $$\rho_p = \tfrac12 \min_{z^q \in Z} \Big\{ \frac{\alpha_{pq} - \alpha_{pp}}{e^{\mathsf T}(z^q - z^p)} \;\Big|\; e^{\mathsf T}(z^q - z^p) > 0 \Big\}$$
--   of (3.6) satisfies
--   $$\rho_p > 0.$$
--
--   This is the first sentence of the proof of Theorem 3.4 ("By Lemma 3.3 and the construction of $\rho_p$ in (3.6), $\rho_p > 0$"): each quotient in the minimum is positive.
--
--   **Formalization Note** When no $z^q \in Z$ has $e^{\mathsf T}(z^q - z^p) > 0$ the minimum in (3.6) is empty; the definition then sets $\rho_p = 1$, so the claim has content only when the index set is nonempty. A vector $z^q$ with $e^{\mathsf T}(z^q - z^p) > 0$ cannot satisfy $z^q \le z^p$, so the corrected Lemma 3.3 applies to every term.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 332, proof of Theorem 3.4, first sentence; eq. (3.6)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_IdealVector
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff
import Definitions.Def_SteuerChoo_Discrete_Weights

namespace SteuerChoo.Discrete

/-- Proof of **Theorem 3.4** (Steuer–Choo 1983, p. 332), first sentence: "By Lemma 3.3 and the
construction of `ρ_p` in (3.6), `ρ_p > 0`." Here `z*` is an ideal criterion vector and `zᵖ ∈ N`. -/
theorem rhoP_pos {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ)
    (hideal : IsIdealVector Z zstar) (zp : Fin k → ℝ) (hp : zp ∈ nondominated Z) :
    0 < rhoP Z zstar zp := by sorry

end SteuerChoo.Discrete
