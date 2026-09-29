-- Prove2me | Theorems.Thm_RobustLP_Counterpart_rc_extension_of_beta
-- name    : RobustLP.Counterpart.rc_extension_of_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:29:32.750808+00:00
-- url     : https://prove2.me/theorems/32e5642a-3f0f-4984-89b0-65041ebb3403
-- title:
--   Sufficient condition for extending $x$ to a feasible solution of (RC): $\sum_ja_{ij}x_j+\epsilon\beta_i(x)\le b_i^+$
-- statement:
--   Let an uncertain linear program with uncertain-entry sets $J_i$ be given, and let $\epsilon>0$, $\delta>0$, $\Omega>0$. For $x\in\mathbb{R}^n$ put
--   $$
--   \beta_i(x) = \Omega\sqrt{\sum_{j\in J_i}a_{ij}^2x_j^2},\qquad b_i^+ = b_i+\delta\max[1,|b_i|].
--   $$
--   If $x$ is feasible for the nominal problem (LP) and
--   $$
--   \sum_j a_{ij}x_j + \epsilon\,\beta_i(x) \le b_i^+ \qquad \forall i,
--   $$
--   then there exist $y=(y_{ij})$ and $z=(z_{ij})$ such that $(x,y,z)$ is feasible for (RC[ε, δ, Ω]).
--
--   Compared with the necessary and sufficient condition $\sum_j a_{ij}x_j+\epsilon\alpha_i(x)\le b_i^+$ for (IRC), with $\alpha_i(x)=\sum_{j\in J_i}|a_{ij}||x_j|$, this shows how much less restrictive (RC) can be when the sets $J_i$ are large.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 420, §3.1, 'while a sufficient condition for x to admit an extension to a feasible solution of (RC) is …'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts

namespace RobustLP.Counterpart

/-- **Sufficient condition for extending `x` to (RC)** (Ben-Tal–Nemirovski 2000, §3.1, p. 420).
For `ε > 0`, `δ > 0`, `Ω > 0`: if `x` is feasible for (LP) and
`∑_j a_{ij} x_j + ε β_i(x) ≤ b_i + δ max[1, |b_i|]` for every `i`, where
`β_i(x) = Ω √(∑_{j ∈ J_i} a_{ij}² x_j²)`, then `x` extends to a feasible solution `(x, y, z)` of
(RC[ε, δ, Ω]). -/
theorem rc_extension_of_beta {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω) (x : Fin n → ℝ)
    (hLP : L.NominalFeasible x)
    (hβ : ∀ i : Fin m, ∑ j, L.A i j * x j +
      ε * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2)) ≤ L.bPlus δ i) :
    ∃ y z : Fin m → Fin n → ℝ, L.RCFeasible ε δ Ω x y z := by sorry

end RobustLP.Counterpart
