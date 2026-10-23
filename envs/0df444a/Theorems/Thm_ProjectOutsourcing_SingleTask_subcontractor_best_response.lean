-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_subcontractor_best_response
-- name    : ProjectOutsourcing.SingleTask.subcontractor_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:10.712982+00:00
-- url     : https://prove2.me/theorems/acddba8a-4aa3-48a7-984b-ed4404ea1829
-- title:
--   §3.2, p. 10 — for p ≥ 0 the subcontractor's profit is concave in r, and every optimal work rate satisfies the first-order condition (one-sided at r̂ = 0)
-- statement:
--   Fix a contract form $m\in\{FP,TF{+},TF,TB,CS,C{+}\}$ and an admissible contract term $\Psi^m=(p,\beta)$ with final payment $p\ge 0$. Under Assumptions 1–2,
--
--   1. the subcontractor's profit $r\mapsto\Pi^m_S(\Psi^m,r)$ is concave on $[0,\infty)$;
--   2. if $\hat r\ge 0$ maximizes $\Pi^m_S(\Psi^m,\cdot)$ on $[0,\infty)$, then $\Pi^m_S(\Psi^m,\cdot)$, restricted to $[0,\infty)$, is differentiable at $\hat r$ and
--   $$\frac{\partial \Pi^m_S}{\partial r}\Big|_{r=\hat r}=0$$
--   (a two-sided derivative when $\hat r>0$, the right derivative when $\hat r=0$).
--
--   This is the implementation stage of the two-stage game: it is how the client anticipates the subcontractor's work rate $\hat r^m(\Psi^m)$ when the contract is negotiated.
--
--   **Formalization Note** Two restrictions relative to the page's sentence are added and disclosed. First, $p\ge 0$: with $p<0$ the term $p\,\mathbb E[e^{-\alpha T}]$ is convex in $r$ and the concavity claim can fail. Second, the derivative is taken within $[0,\infty)$, so that at the corner $\hat r=0$ (which, for $p\ge 0$, can only be optimal when $p=0$) it is the right derivative; for $p<0$ the corner optimum $\hat r=0$ has a strictly negative right derivative, which is another reason for $p\ge 0$. Existence of a maximizer is not claimed: under C+ (or CS with $\beta=1$) and $p>0$ the profit $p\,\mathbb E[e^{-\alpha Z/r}]$ increases without attaining its supremum.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 10, §3.2, Implementation Stage

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem subcontractor_best_response (M : Model) (hM : M.Valid) (m : Form) (Ψ : ℝ × ℝ)
    (hΨ : Ψ ∈ params m) (hp : 0 ≤ Ψ.1) :
    ConcaveOn ℝ (Set.Ici 0) (subProfit M m Ψ) ∧
      ∀ r, 0 ≤ r → IsMaxOn (subProfit M m Ψ) (Set.Ici 0) r →
        HasDerivWithinAt (subProfit M m Ψ) 0 (Set.Ici 0) r := by sorry

end ProjectOutsourcing.SingleTask
