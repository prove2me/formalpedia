-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_farkas_11
-- name    : RobustUncLP.WorstCase.farkas_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:52:06.910449+00:00
-- url     : https://prove2.me/theorems/1230f72c-6f2a-4972-901b-feffc1cef71f
-- title:
--   (11), §2.2, proof of Proposition 2.1, p. 5 — Farkas: inconsistency of (10) gives λ_ip ≥ 0, μ > 0 with Σλ_ip a_i^p + μf = 0
-- statement:
--   Let $A_1,\dots,A_N$ be real $m\times n$ matrices, $f\in\mathbb R^{n}$, and write $a_i^{p}\in\mathbb R^{n}$ for the $i$-th row of $A_p$. If the system $A_1x\ge 0,\dots,A_Nx\ge0,\ f^{T}x = 1$ has no solution, then there exist nonnegative reals $\lambda_{ip}$ ($i = 1,\dots,m$, $p = 1,\dots,N$) and a real $\mu$ such that
--   $$\sum_{i=1}^{m}\sum_{p=1}^{N}\lambda_{ip}\,a_i^{p} + \mu f = 0,\qquad \mu > 0. \tag{11}$$
--
--   This is the instance of Farkas' Lemma used in the proof of Proposition 2.1; the multipliers are then used to average the rows of the instances.
--
--   **Formalization Note** Indices $i$ and $p$ range over `Fin m` and `Fin N`; the row $a_i^p$ is `A p i`.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, §2.2, proof of Proposition 2.1, (11)

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem farkas_11 {m n N : ℕ} (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ)
    (h : ¬ ∃ x : Fin n → ℝ, (∀ p, 0 ≤ A p *ᵥ x) ∧ f ⬝ᵥ x = 1) :
    ∃ (lam : Fin m → Fin N → ℝ) (μ : ℝ), (∀ i p, 0 ≤ lam i p) ∧ 0 < μ ∧
      (∑ i, ∑ p, lam i p • A p i) + μ • f = 0 := by sorry

end RobustUncLP.WorstCase
