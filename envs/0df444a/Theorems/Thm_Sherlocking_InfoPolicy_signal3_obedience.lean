-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_signal3_obedience
-- name    : Sherlocking.InfoPolicy.signal3_obedience
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:23.962162+00:00
-- url     : https://prove2.me/theorems/ebbd0d89-7dc7-4cc6-85f1-e984f7f308ed
-- title:
--   §5.1, p. 15 (PDF 17) — signal (3) induces the full commitment outcome iff (OC0) holds; (OC1) always holds
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$, and let $0\le r<1-K$. Let $\sigma_3$ be signal (3):
--   $$\Pr(x=1\mid\theta)=\begin{cases}\alpha(\theta;r) & \text{if }\theta_P(r)\le\theta\le1,\\ 0&\text{otherwise,}\end{cases}$$
--   and let the platform play the obedient strategy (enter iff $x=1$). Then:
--
--   1. $\sigma_3$ is an information policy (a measurable family of probability distributions on $\{0,1\}$);
--   2. with entry set $[\theta_S(r),1]$, the outcome is the full commitment outcome: exactly the types in $[\theta_S(r),1]$ enter, each facing the full-commitment entry probability;
--   3. signal $\sigma_3$, the obedient strategy and the entry set $[\theta_S(r),1]$ form an equilibrium at fee $r$ if and only if (OC0) holds:
--   $$\mathbb E[\theta\mid x=0;\ \theta\ge\theta_S(r)]\le\theta_P(r);$$
--   4. if $\theta_P(r)<1$, then (OC1) holds: $\mathbb E[\theta\mid x=1;\ \theta\ge\theta_S(r)]>\theta_P(r)$.
--
--   Together these show that signal (3) induces the full commitment outcome exactly when (OC0) holds.
--
--   **Formalization Note** The page's "if and only if (OC0) and (OC1)" is split: clause 3 states the equivalence with (OC0) alone and clause 4 records that (OC1) always holds, as the page says right after. Clause 4 assumes $\theta_P(r)<1$, since otherwise $x=1$ has probability $0$ and (OC1) is a $0/0$ claim. $\delta<1$ and $r<1-K$ are added (the latter makes the conditioning event of (OC0) have positive probability).
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 15 (PDF 17), §5.1, Eq. (3), (OC0), (OC1)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem signal3_obedience (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r) (hrK : r < 1 - K) : IsInfoPolicy (signal3 K δ r) ∧ ImplementsCommitment K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) ∧ (IsEquilibrium K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) ↔ OC0 K δ r) ∧ (thetaP K δ r < 1 → OC1 K δ r) := by sorry

end Sherlocking.InfoPolicy
