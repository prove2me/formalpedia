-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_proposition_5
-- name    : TimeLockedSales.Reform.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:40.454985+00:00
-- url     : https://prove2.me/theorems/35e59939-7c48-4dde-b0f0-bb88fe5725cb
-- title:
--   Proposition 5, p. 18 — optimal platform revenue equals the values of (9) and LP (11)
-- statement:
--   Under the campaign assumptions and $v^*\le v_0<v^{**}$, there is a value $\pi$ with four properties.
--
--   1. LP (11) attains $\pi$.
--   2. The recommendation-policy program (9) attains $\pi$.
--   3. $\pi$ is the least upper bound of expected revenue over all finite-message information policies whose customers use the Bayesian purchase rule (2).
--   4. Every optimum $y$ of LP (11), converted by (10) to $z_t(n)=\sum_i y_t^i(n)$ and $r_t^i(n)=y_t^i(n)/z_t(n)$ when $z_t(n)>0$, gives a feasible optimum of (9), with any (R)-vector when $z_t(n)=0$.
--
--   In particular, the value identity is
--   $$\pi=\max_{y\text{ feasible for (11)}}L(y)=\max_{(r,z)\text{ feasible for (9)}}J(r,z)=\sup_{\sigma}R(\sigma).$$
--   This is the paper's reduction of dynamic information design to a finite linear program.
--
--   **Formalization Note.** The paper writes “max” over original policies. The statement uses a least upper bound there because weak IC inequalities at the tie endpoints may prevent the LP recovery from being realized by the Bayesian response rule; it still asserts maxima for (9) and (11). Message spaces are finite, reflecting the sums over histories in the paper. The original-policy supremum ranges over all such policies, not just recommendations. The $v^*$ boundary is assigned to following the signal, and obedience is checked on realized signal–message pairs. Lean histories of length $t$ precede customer $t+1$; (9) and (11) retain the printed one-based time indices and zero boundary terms. No additional restrictions on $T$, $q$, or $v_0$ are imposed.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 18, Proposition 5, (10)–(11); proof pp. 42–43, (B.17)–(B.18)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Proposition 5, p. 18: (11), (9), and (3) have the same value, with recovery (10). -/
theorem proposition_5 (P : Params) (hS : P.Standing) (hR : P.Region) :
    ∃ π : ℝ,
      IsGreatest {J | ∃ y, FeasibleLP P y ∧ J = objLP P y} π ∧
      IsGreatest {J | ∃ r z, Feasible9 P r z ∧ J = obj9 P r z} π ∧
      IsLUB (AchievableRevenue P) π ∧
      ∀ y, FeasibleLP P y → objLP P y = π →
        ∀ r, Recovers P y r →
          Feasible9 P r (zOf y) ∧ obj9 P r (zOf y) = π := by sorry

end TimeLockedSales.Reform
