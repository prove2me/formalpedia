-- Prove2me | Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1
-- name    : ReadmissionsHRRP.HRRPI.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:08.115719+00:00
-- url     : https://prove2.me/theorems/683b416a-f8ca-404a-9f2a-f870f980fb01
-- title:
--   Proposition 1, p. 14 — under HRRP-I a symmetric equilibrium exists, every symmetric equilibrium has r̃ < r*, c̃ > c*, and with N = 2 none is asymmetric
-- statement:
--   Consider $N\ge 2$ identical hospitals. Hospital $i$ chooses a readmission rate $r_i$ and a marginal cost $c_i$ in the box $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$ at investment cost $R(r_i,c_i)$, where $R$ satisfies the standing assumptions of §3.1 (twice continuously differentiable, decreasing, jointly convex, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$, $R_{cr}\ge0$) and the first best is interior. Under HRRP-I the regulator pays hospital $i$
--   $$T_i=\bar c_i\lambda(1+r_i)-\frac{1}{\bar r_i}(r_i-\bar r_i)(1+r_i)\bar c_i\lambda+\bar R_i,$$
--   with $\bar c_i,\bar r_i,\bar R_i$ the averages of the other hospitals' costs, readmission rates and investment costs, and the hospital maximizes $\Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i)$ over $B$. Let $(r^*,c^*)$ be the maximizer of the welfare $S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c)$ over $B$. Then:
--
--   1. there exists at least one symmetric pure-strategy Nash equilibrium $(\tilde r,\tilde c)$;
--   2. every symmetric equilibrium satisfies
--   $$\tilde r<r^*,\qquad \tilde c>c^*;$$
--   3. if $N=2$, every equilibrium is symmetric: there is no asymmetric equilibrium.
--
--   The result shows that the multiplier $(1+r_i)/\bar r_i$ of the HRRP penalty makes hospitals over-invest in readmission reduction and, as a consequence, under-invest in cost reduction relative to the first best.
--
--   **Formalization Note** $\lambda$ is written `lam`; $\lambda>0$ and $N\ge2$ are added as hypotheses (the second because (6) divides by $N-1$). The paper's boundary conditions of Appendix A, not part of the cited manuscript, are replaced by the hypothesis that every maximizer of $S$ over $B$ is interior, which the paper says those conditions ensure. Claim 2 quantifies over every maximizer of $S$, of which there is exactly one by Lemma 1. Claim 3 does not depend on $N$ and is stated for the two-hospital game.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, author-accepted manuscript, LBS Research Online eprint 1402 (Management Science 67(4), 2021, doi:10.1287/mnsc.2020.3649), p. 14, Proposition 1

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting

namespace ReadmissionsHRRP.HRRPI

/-- Proposition 1 (p. 14): under HRRP-I, for every number `N ≥ 2` of hospitals there is a symmetric
equilibrium, every symmetric equilibrium `(r̃, c̃)` has `r̃ < r*` and `c̃ > c*` (`(r*, c*)` the
maximizer of the welfare `S` over the box), and with two hospitals there is no asymmetric
equilibrium. -/
theorem proposition_1 (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    (∃ p : ℝ × ℝ, M.IsSymEqI N p) ∧
    (∀ p : ℝ × ℝ, M.IsSymEqI N p →
      ∀ xs : ℝ × ℝ, M.IsFirstBest xs → p.1 < xs.1 ∧ xs.2 < p.2) ∧
    (∀ x : Fin 2 → ℝ × ℝ, M.IsEqI 2 x → x 0 = x 1) := by sorry

end ReadmissionsHRRP.HRRPI
