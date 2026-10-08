-- Prove2me | Theorems.Thm_SennottDP_BOR_acoe_sufficient_conditions
-- name    : SennottDP.BOR.acoe_sufficient_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:29:37.226968+00:00
-- url     : https://prove2.me/theorems/1adfe607-e246-4115-a5c3-e2d50b67fa9a
-- title:
--   Theorem 7.4.3 — four sufficient conditions for the ACOE at a state
-- statement:
--   Assume the (SEN) assumptions hold for $z$ with function $M$ and constant $L$, let $J$ be the constant of Theorem 7.2.3(i), $h$ a limit function and $e$ a stationary policy realizing the minimum in the ACOI (7.9). Define the nonnegative discrepancy function $\Phi$ by
--   $$
--   J+h(i)=C(i,e)+\Phi(i)+\sum_jP_{ij}(e)h(j),\qquad i\in S.\qquad(7.28)
--   $$
--   Then $\Phi(i)=0$, and hence (7.9) is an equality at the particular state $i$, under any of the following conditions:
--
--   1. There is a nonempty set $G$ with $e\in\Re(i,G)$ and $\sum_{j\in G}M(j)P_e(X_T=j)<\infty$ (the assumptions of Lemma 7.4.2). Then also $e\in\Re^*(i,G)$ and $h(i)=c_{iG}(e)-Jm_{iG}(e)+E_e[h(X_T)\mid X_0=i]$, $T$ the first passage time.
--   2. $e\in\Re(i,z)$. Then also $e\in\Re^*(i,z)$ and $h(i)=c_{iz}(e)-Jm_{iz}(e)$.
--   3. The Markov chain induced by $e$ is positive recurrent at $i$.
--   4. $\sum_jP_{ij}(a)M(j)<\infty$ for $a\in A_i$.
--
--   The ACOI may be strict (Example 7.3.1); this theorem identifies where it is an equality.
--
--   **Formalization Note** $\Phi$ is computed in the extended reals; each of the four parts concludes both $\Phi(i)=0$ and the equality $J+h(i)=\min_a\{C(i,a)+\sum_jP_{ij}(a)h(j)\}$ at $i$. In parts 1 and 2 the identities are stated in the reals, which is meaningful because they also assert $e\in\Re^*$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 141–142, Theorem 7.4.3, (7.28)

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Theorem 7.4.3, pp. 141–142. Assume (SEN) holds for `z` with `Mf` and `L`,
let `J` be the constant of Theorem 7.2.3(i), `h` a limit function, and `e` a stationary policy
realizing the minimum in the ACOI (7.9). Let `Φ` be the discrepancy function (7.28). Then at the
state `i`, `Φ(i) = 0` and hence (7.9) is an equality at `i` under each of the conditions:
(i) `e ∈ ℜ(i,G)` for a nonempty `G` with `∑_{j∈G} Mf(j) P_e(X_T = j) < ∞`; then also
`e ∈ ℜ*(i,G)` and `h(i) = c_{iG}(e) − J m_{iG}(e) + E_e[h(X_T) | X_0 = i]`;
(ii) `e ∈ ℜ(i,z)`; then also `e ∈ ℜ*(i,z)` and `h(i) = c_{iz}(e) − J m_{iz}(e)`;
(iii) the Markov chain induced by `e` is positive recurrent at `i`;
(iv) `∑_j P_{ij}(a) Mf(j) < ∞` for `a ∈ A_i`. -/
theorem acoe_sufficient_conditions {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENWith M z Mf L) (J : ℝ) (hJ0 : 0 ≤ J)
    (hJ : ∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * valueFn M α i) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal J)))
    (h : S → ℝ) (hh : IsLimitFunction M z h) (e : StationaryPolicy M) (he : RealizesMin M h e)
    (i : S) :
    (∀ G : Set S, G.Nonempty → InR e.toPolicy i G →
      ∑' j : G, ENNReal.ofReal (Mf j) * hitDist e.toPolicy i G j < ⊤ →
        discrepancy M J h e i = 0 ∧ ((J + h i : ℝ) : EReal) = acoiRHS M h i ∧
        InRStar e.toPolicy i G ∧ Summable (fun j => h j * (hitDist e.toPolicy i G j).toReal) ∧
        h i = (passageCost e.toPolicy i G).toReal - J * (meanPassage e.toPolicy i G).toReal
          + ∑' j, h j * (hitDist e.toPolicy i G j).toReal) ∧
    (InR e.toPolicy i {z} →
        discrepancy M J h e i = 0 ∧ ((J + h i : ℝ) : EReal) = acoiRHS M h i ∧
        InRStar e.toPolicy i {z} ∧
        h i = (passageCost e.toPolicy i {z}).toReal - J * (meanPassage e.toPolicy i {z}).toReal) ∧
    (PosRecurrent e.toPolicy i →
        discrepancy M J h e i = 0 ∧ ((J + h i : ℝ) : EReal) = acoiRHS M h i) ∧
    ((∀ a ∈ M.A i, ∑' j, M.P i a j * ENNReal.ofReal (Mf j) < ⊤) →
        discrepancy M J h e i = 0 ∧ ((J + h i : ℝ) : EReal) = acoiRHS M h i) := by sorry

end SennottDP.BOR
