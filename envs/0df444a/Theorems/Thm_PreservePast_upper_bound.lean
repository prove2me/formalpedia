-- Prove2me | Theorems.Thm_PreservePast_upper_bound
-- name    : PreservePast.upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:28.452626+00:00
-- url     : https://prove2.me/theorems/895f9b98-857d-4080-9b97-346ce4aa3ee5
-- title:
--   (70) and §C.5 — the deterministic upper bound $B\le C\mathcal L^3(F_C+F_R)$
-- statement:
--   There is an absolute constant $C>0$ such that for all $1\le r\le m\le n$, all $0<\epsilon\le2^{-28}$ and every checkpoint $W_0\in\mathbb R^{m\times n}$, some deterministic code of width
--   $$
--   B\le C\mathcal L^3(F_C+F_R),\qquad F_C=n^2\log_2\Big(1+\frac1{n\epsilon}\Big),\quad F_R=nr\log_2\Big(1+\frac1{r\epsilon^2}\Big),\quad\mathcal L=\log_2\frac2\epsilon,
--   $$
--   returns, for every old task and every promised unit query $(x,p)$ (rank $r$, radius $\sqrt3$), an update with $Hx=p$, $\operatorname{rank}H\le r$, $\|H\|_F\le\sqrt3$ and $f(H)\le\epsilon$.
--
--   This is the upper half of Theorem 4: memory proportional to the useful response directions, not to the raw loss coefficients.
--
--   **Formalization Note** One task ($K=1$), exact fit ($\xi=0$). Unlike the goal, there is no hypothesis $n\ge N_\beta$.
--
--   Differences from the source:
--   - generalization: upper bound of (16) under Theorem 4's assumptions, including n ≥ N_β → no hypothesis n ≥ N_β; reason: the upper-bound proof of §C.5 does not use it; adding it back gives the source's claim
--   - generalization: B_full(1, n, m, r; ϵ, 0, √3, β) ≤ C𝓛³(F_C + F_R) → a deterministic code of that width succeeds with certainty for every task and promised query; reason: the paper states the upper bound is deterministic (p.6); it implies the B_full bound for every β (verification file)
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.5, pp.22–24 (PDF pp.24–26), (70); §3.1, p.6, remark after Theorem 4

import Mathlib
import Definitions.Def_PreservePast_DetAchieves
import Definitions.Def_PreservePast_FC

namespace PreservePast

/-- **The upper bound of (16), §C.5 and (70).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.5, pp.22–24 (PDF pp.24–26):
"B ≤ CF_C + Cn min{m, r + ϵ^{−1}}𝓛³ ≤ C𝓛³(F_C + nr). (70) … For r > ϵ^{−2}, the Frobenius-gradient
branch of Theorem 9 costs O(F_C + F_F) with F_F = nm log₂(1 + 1/(mϵ²)) ≤ n/((ln 2)ϵ²) ≤ 2F_R. For
r = 1, its operator-gradient branch costs O(F_C)"; p.6: "The upper bound is deterministic: for
every fixed history and every promised unit query (x, p), it returns Hx = p, rank H ≤ r,
‖H‖_F ≤ √3, and f(H) ≤ ϵ."

There is an absolute constant `C > 0` such that for all `1 ≤ r ≤ m ≤ n`, `0 < ϵ ≤ 2^{−28}` and every
checkpoint `W₀`, some deterministic code of width `B ≤ C𝓛³(F_C + F_R)` succeeds (with `K = 1`,
`ξ = 0`, `R = √3`) for every task and every promised query.

**Formalization Note.** This is part (ii) of the goal without the hypothesis `n ≥ N_β`, which the
upper-bound proof of §C.5 does not use. -/
theorem upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n r : ℕ) (ε : ℝ) (W₀ : Matrix (Fin m) (Fin n) ℝ),
      1 ≤ r → r ≤ m → m ≤ n → 0 < ε → ε ≤ (2 : ℝ) ^ (-28 : ℤ) →
      ∃ B : ℕ, (B : ℝ) ≤ C * calL ε ^ 3 * (FC n ε + FR n r ε) ∧
        ∃ (enc : (Fin 1 → Task W₀) → Fin (2 ^ B))
          (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
          DetAchieves enc dec r ε 0 (Real.sqrt 3) := by sorry

end PreservePast
