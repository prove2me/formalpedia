-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_proposition_1
-- name    : SurgeAppt.FirstAvail.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:00.580977+00:00
-- url     : https://prove2.me/theorems/1ea7cd0d-136b-4859-8a38-b5b7090304e0
-- title:
--   Proposition 1, p. 12 — under (13), the First-Available policy is optimal among all admissible Markov scheduling policies
-- statement:
--   Consider the appointment-scheduling model of §3 with the surge cost structure (5), under its standing assumptions: horizon $D\ge1$; base and surge capacities $K_b, K_s$ with $K = K_b+K_s$; surge cost $c_s\ge0$ and failure cost $c_F>0$; failure probability $p_F\in(0,1)$, $p_{\bar F} = 1-p_F$; show probability $p_S\in[0,1]$, $p_{\bar S}=1-p_S$; post-appointment failure probabilities $p_{F|S}<p_{F|\bar S}$ in $[0,1]$; discount factor $\beta\in(0,1)$; i.i.d. arrivals bounded by $M\ge1$. Suppose condition (13) holds:
--
--   $$
--   \frac{c_s}{c_F}\le\min_{1\le d<d'\le D}\ \big(p_{\bar F}^{d'-d}\beta^{d'-d}-1\big)\big(p_Sp_{F|S}+p_{\bar S}p_{F|\bar S}\big)+\frac{\sum_{i=d}^{d'-1}\beta^{i+1}p_Fp_{\bar F}^i}{p_{\bar F}^d\beta^d}.
--   $$
--
--   Then the **First-Available (FA)** policy, which books each period's requests into the earliest periods $1,2,\dots,D$ with free (base, then surge) slots, is admissible and optimal: for every admissible policy $\pi$ and every valid initial appointment book $\mathbf S^0$,
--
--   $$
--   V_{\mathrm{FA}}(\mathbf S^0)\le V_\pi(\mathbf S^0),
--   $$
--
--   where $V_\pi$ is the expected total discounted cost (9).
--
--   The condition compares, for every pair of delays $d<d'$, the cost of a surge appointment at delay $d$ with the extra discounted failure cost of waiting until $d'$; when surge is cheap enough for every pair, using surge capacity as early as needed is optimal regardless of the state and of the arrival distribution.
--
--   **Formalization Note** The competitors are all admissible Markov deterministic policies, possibly non-stationary ($U^t$ depends on $t$, the current book and the current arrivals); the paper's class of non-anticipative policies is reduced to this class on the strength of its own remark after (11) that a stationary optimal policy exists. History-dependent and randomized policies are not modelled. The value averages over the first period's arrivals $A^0$, as $V_\pi(\mathbf S^0)$ in (9). The minimum over pairs in (13) is written as "for every pair", vacuous when $D=1$ (then FA is the only admissible policy). The hypotheses $D\ge1$, $c_s\ge0$, $c_F>0$, $0<p_F<1$ and the probability ranges are added: they are implicit on the page, and (13) divides by $c_F$ and $p_{\bar F}^d\beta^d$. The admissibility of FA is part of the conclusion.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), p. 12, Proposition 1, (13)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- Proposition 1 (First Available (FA)), p. 12: under the standing assumptions and condition (13),
the First-Available policy is admissible and optimal: its value (9) is at most the value of every
admissible Markov deterministic policy, from every valid initial appointment book. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (h13 : Condition13 P) :
    IsAdmissible P (faPolicy P) ∧
      ∀ π : Policy P, IsAdmissible P π →
        ∀ s : Book P, Valid P s → value P (faPolicy P) s ≤ value P π s := by sorry

end SurgeAppt.FirstAvail
