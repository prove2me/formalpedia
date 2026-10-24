-- Prove2me | Theorems.Thm_SwitchbackExp_Design_relaxation_bound
-- name    : SwitchbackExp.Design.relaxation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:55.491717+00:00
-- url     : https://prove2.me/theorems/94a11eb6-2e5a-4095-b55e-d2539668a768
-- title:
--   Proof of Theorem 2, pp. ec22–ec23 — for T = nm, n ≥ 4, the objective (7) is ≥ 16mT − 32m², with equality exactly at 𝕋*
-- statement:
--   Let $m\ge1$, $n\ge4$ and $T=nm$. For every regular point set $\mathbb T=\{t_0=1<t_1<\dots<t_K\}\subseteq[T]$, with $t_{K+1}=T+1$, the objective of the subset selection problem (7) satisfies
--   $$4\sum_{k=0}^{K}(t_{k+1}-t_k)^2+8m(t_K-t_1)+4m^2K-4m^2+4\sum_{k=1}^{K-1}\bigl[(m-t_{k+1}+t_k)^+\bigr]^2\ \ge\ 16mT-32m^2,$$
--   and equality holds if and only if
--   $$\mathbb T=\mathbb T^*=\{1,\,2m+1,\,3m+1,\,\dots,\,(n-2)m+1\}.$$
--
--   This is the integer content of the continuous relaxation argument in the proof of Theorem 2: the relaxed optimum $a=2m$, $b=m$ is attained by an integer design, which is therefore optimal for (7), and it is the only one.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), EC.3.6.1, proof of Theorem 2, pp. ec22–ec23

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Proof of Theorem 2, EC.3.6.1 (pp. ec22–ec23): for `T = n m` with `m ≥ 1`, `n ≥ 4`, the objective (7)
of every regular point set is at least `16 m T − 32 m²`, with equality exactly at
`𝕋* = {1, 2m+1, …, (n−2)m+1}`. -/
theorem relaxation_bound (m n T : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (hT : T = n * m) :
    ∀ P : Finset ℕ, IsRegularPoints T P →
      16 * (m : ℝ) * T - 32 * (m : ℝ) ^ 2 ≤ objective7 m T P ∧
      (objective7 m T P = 16 * (m : ℝ) * T - 32 * (m : ℝ) ^ 2 ↔ P = optPoints m n) := by sorry

end SwitchbackExp.Design
