-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_14
-- name    : PQNormIPM1352.Main.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:32.984317+00:00
-- url     : https://prove2.me/theorems/81913cf7-35f7-4917-a3c3-69571d390b74
-- title:
--   Lemma 14 — path update step: $\lambda_{(1+\alpha)\eta}(x)\le(1+\alpha)\lambda_\eta(x)+\alpha\sqrt\nu$
-- statement:
--   Let $F$ be a $\nu$-self-concordant barrier for $K \subseteq \mathbb R^N$, let $c \in \mathbb R^N$, and let $x \in \mathrm{int}(K)$. For any $\eta > 0$ and $\alpha > 0$, the scaled barrier parameter $\eta^+ = (1+\alpha)\eta$ satisfies
--   $$\lambda_{\eta^+}(x) \le (1+\alpha)\,\lambda_\eta(x) + \alpha\sqrt\nu,$$
--   where $\lambda_\eta(x)$ is the Newton decrement of $\Phi_\eta = F + \eta\langle c,\cdot\rangle$ at $x$.
--
--   It controls how far the current point is from the new central-path point after each increase of $\eta$ in Theorem 12.
--
--   Differences from the source:
--   - encoding: λ_η(x) = ‖H(x)⁻¹∇Φ_η(x)‖_x → the Newton decrement with Mathlib's matrix inverse, no invertibility hypothesis; reason: equal to the source's quantity when H(x) is invertible; for a singular Hessian both decrements are 0 and the inequality still holds
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 14, printed p. 23 (PDF p. 24); [Ren01, eq. 2.4.5]

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_IPM

namespace PQNormIPM1352.Main

/-- **Lemma 14** (path update step; Pirazzini–Spielman, STOC 2027 #1352, p. 23). Let `F` be a
`ν`-self-concordant barrier for `K`, `c ∈ ℝᴺ`, and `x ∈ int(K)`. For any `η > 0` and `α > 0`, the
scaled parameter `η⁺ = (1 + α)η` satisfies `λ_{η⁺}(x) ≤ (1 + α) λ_η(x) + α √ν`. -/
theorem lemma_14 {N : ℕ} (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ) (hF : IsNuSCB K F ν)
    (c : Vec N) (x : Vec N) (hx : x ∈ interior K) (η α : ℝ) (hη : 0 < η) (hα : 0 < α) :
    newtonDecrement (penalized F c ((1 + α) * η)) x ≤
      (1 + α) * newtonDecrement (penalized F c η) x + α * Real.sqrt ν := by sorry

end PQNormIPM1352.Main
