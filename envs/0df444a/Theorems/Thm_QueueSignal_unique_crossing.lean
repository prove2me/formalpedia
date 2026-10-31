-- Prove2me | Theorems.Thm_QueueSignal_unique_crossing
-- name    : QueueSignal.unique_crossing
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:44.403101+00:00
-- url     : https://prove2.me/theorems/fc395667-50a2-4207-b3f7-071a0105088b
-- title:
--   §4.2 — $\lambda^O(\delta)$ and $\lambda^U(\delta)$ have a unique crossing point $\hat\lambda$
-- statement:
--   Let $\mu,\theta>0$, $V_H>V_L>\theta/\mu$, $0<\delta<1$, and fix a belief $d\in[0,1]$. Regard the effective arrival rates $\lambda^O(d)$ of (1) and $\lambda^U(d)$ of (3) as functions of the potential arrival rate $\lambda>0$. Then there is exactly one $\hat\lambda>0$ with
--   $$\lambda^O(d)\big|_{\lambda=\hat\lambda}=\lambda^U(d)\big|_{\lambda=\hat\lambda},$$
--   and moreover $\lambda^O(d)<\lambda^U(d)$ for $0<\lambda<\hat\lambda$, while $\lambda^O(d)>\lambda^U(d)$ for $\lambda>\hat\lambda$.
--
--   At $d=\delta$ this is the crossing point $\hat\lambda$ of Proposition 1: below it a server facing customers who hold the prior belief prefers to conceal its queue, above it to reveal it.
--
--   **Formalization Note** The crossing point is asserted to exist and be unique among positive $\lambda$; it is not a parameter.
--
--   Differences from the source:
--   - generalization: the unique crossing point of λ^O(δ) and λ^U(δ) (at the prior δ) → the same for every belief d ∈ [0, 1]; reason: d = δ is the source's statement
--   - generalization: "unique crossing point" → existence and uniqueness of the crossing, plus λ^O < λ^U on (0, λ̂) and λ^O > λ^U on (λ̂, ∞); reason: the sign clauses are what "crossing" means and what p.549 uses ("the server prefers to conceal the queue if λ^U(δ) > λ^O(δ) and to reveal it otherwise"); dropping them gives the printed statement
--   - encoding: n(δ^R) = ⌊[δ^R V_H + (1 − δ^R)V_L]µ/θ⌋ − 1 used as a summation bound → computed in ℤ and converted with Int.toNat; reason: under V_L > θ/µ and a belief in [0, 1] it is ≥ 0, so the conversion changes no instance
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §4.2, paragraph before Proposition 1, p.549

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

namespace QueueSignal

/-- **The unique crossing point `λ̂`** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §4.2, p.549, PDF p.8: "We denote the unique
crossing point of `λ^O(δ)` and `λ^U(δ)` as `λ̂`").

For every belief `d ∈ [0, 1]` (in particular the prior `δ`), the functions `λ ↦ λ^O(λ, d)` and
`λ ↦ λ^U(λ, d)` on `(0, ∞)` cross exactly once, at some `λ̂ > 0`; below `λ̂` concealing gives the
larger effective arrival rate (`λ^O < λ^U`), above it revealing does (`λ^O > λ^U`). -/
theorem unique_crossing (P : Params) (hP : P.Valid) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    ∃ lhat : ℝ, 0 < lhat ∧ lamO P lhat d = lamU P lhat d ∧
      (∀ lam : ℝ, 0 < lam → lamO P lam d = lamU P lam d → lam = lhat) ∧
      (∀ lam : ℝ, 0 < lam → lam < lhat → lamO P lam d < lamU P lam d) ∧
      (∀ lam : ℝ, lhat < lam → lamU P lam d < lamO P lam d) := by sorry

end QueueSignal
