-- Prove2me | Theorems.Thm_Viterbo_cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable
-- name    : Viterbo.cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T07:21:58.300089+00:00
-- url     : https://prove2.me/theorems/d2486c07-c981-456e-96e6-d799717ddccb
-- title:
--   Theorem 2.2 — c_EHZ(K × T) is the minimal action of a closed characteristic, the minimal T°-length of a closed T-billiard, and the minimal T°-length over P(K) with at most n + 1 vertices
-- statement:
--   Let $n \ge 1$, and let $K \subset \mathbb R^n_q$ and $T \subset \mathbb R^n_p$ be convex domains, with the origin in the interior of $T$. There is a real $L$ with $c_{\rm EHZ}(K \times T) = L$ such that:
--   - $L = |\mathcal A(\gamma)|$ for some nonconstant generalized closed characteristic $\gamma$ of $K \times T$;
--   - $L$ is the $T^\circ$-length of some closed $T$-billiard trajectory in $K$, and no closed $T$-billiard trajectory in $K$ is shorter;
--   - $L$ is the $T^\circ$-length of some polygonal curve in $\mathcal P(K)$ with at most $n + 1$ vertices, and no such curve is shorter.
--
--   *Formalization note.* "$\min$" is stated as: the value is attained, and is a lower bound for every candidate. The hypothesis $0 \in \mathrm{int}\,T$ is the standing assumption of §2 (p. 8: "$T \subset \mathbb R^n_p$ be a convex domain which has the origin in its interior"). The dimension is $n \ge 1$: in dimension $0$ there is no boundary to carry a characteristic.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 10, Theorem 2.2, which cites Artstein-Avidan, S. and Ostrover, Y., Bounds for Minkowski billiard trajectories in convex bodies, Int. Math. Res. Not. IMRN 2014, 165–193, https://doi.org/10.1093/imrn/rns216, Theorem 2.13, and Rudolf, D., The Minkowski billiard characterization of the EHZ-capacity of convex Lagrangian products, J. Dynam. Differential Equations 36 (2024) 2773–2791, https://doi.org/10.1007/s10884-022-10228-0, Theorem 1

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable (n : ℕ) (hn : 1 ≤ n)
    (K T : Set (OAI.SymmetricPolar.Position n)) (hK : IsConvexDomain K) (hT : IsConvexDomain T)
    (h0 : (0 : OAI.SymmetricPolar.Position n) ∈ interior T) :
    ∃ L : ℝ, cEHZ (K ×ˢ T) = ENNReal.ofReal L ∧
      (∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic (K ×ˢ T) γ ∧
        (∃ s t, γ s ≠ γ t) ∧ |action γ| = L) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q ∧
        polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), IsClosedBilliard K T q →
        L ≤ polygonLength T q) ∧
      (∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 ∧
        NotTranslatableIntoInterior K q ∧ polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position n), m ≤ n + 1 →
        NotTranslatableIntoInterior K q → L ≤ polygonLength T q) := by
  sorry

end Viterbo
