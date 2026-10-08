-- Prove2me | Theorems.Thm_TsengBCD_Stationary_part_c_windows_eq
-- name    : TsengBCD.Stationary.part_c_windows_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T22:18:36.692297+00:00
-- url     : https://prove2.me/theorems/a6afa2d0-4db0-4959-9dcd-43181f7b04da
-- title:
--   Proof of Theorem 4.1(c), pp. 482–483 — unique block minima force z¹ = z² = ⋯ = z^{T−1}
-- statement:
--   Let $f:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$, $T\ge 0$, and let $z^1,\dots,z^T$ be points and $s^1,\dots,s^T$ blocks such that:
--   1. $f$ has at most one minimum in $x_k$ for $k=s^2,\dots,s^{T-1}$;
--   2. $z^j\in\operatorname{dom}f$ for $j=1,\dots,T$;
--   3. (7) $f(z^j)\le f(z^j+(0,\dots,d_{s^j},\dots,0))$ for all $d_{s^j}$, $j=1,\dots,T$, and $z^j_k=z^{j-1}_k$ for all $k\ne s^j$, $j=2,\dots,T$;
--   4. (8) $f(z^{j-1})\le f(z^{j-1}+(0,\dots,d_{s^j},\dots,0))$ for all $d_{s^j}$, $j=2,\dots,T$.
--
--   Then
--   $$z^{j-1}=z^j\qquad\text{for } j=2,\dots,T-1,$$
--   so $z^1=z^2=\cdots=z^{T-1}$.
--
--   In the proof of Theorem 4.1(c), (7) and (8) say that $d_{s^j}\mapsto f(z^j+(0,\dots,d_{s^j},\dots,0))$ attains its minimum both at $0$ and at $z^{j-1}_{s^j}-z^j_{s^j}$; uniqueness of the minimum point collapses the window, and the cluster point is then a coordinatewise minimum point.
--
--   **Formalization Note.** Stated about the points $z^j$ and blocks $s^j$ alone, with (7), (8) as hypotheses; `limit_chain` produces them from a BCD run. A minimum point of a block section is a point of its effective domain (see the definitions item), which is why $z^j\in\operatorname{dom}f$ is a hypothesis here; in the theorem it follows from (6).
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 482–483, proof of Theorem 4.1(c)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

namespace TsengBCD.Stationary

open Filter Topology

theorem part_c_windows_eq {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (T : ℕ)
    (zs : ℕ → X n) (ss : ℕ → Fin N)
    (huniq : ∀ j, 2 ≤ j → j ≤ T - 1 → AtMostOneMinIn f (ss j))
    (hfin : ∀ j, 1 ≤ j → j ≤ T → f (zs j) ≠ ⊤)
    (h7 : ∀ j, 1 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs j) ≤ f (zs j + Pi.single (ss j) d))
    (h7' : ∀ j, 2 ≤ j → j ≤ T → ∀ k : Fin N, k ≠ ss j → zs j k = zs (j - 1) k)
    (h8 : ∀ j, 2 ≤ j → j ≤ T → ∀ d : EuclideanSpace ℝ (Fin (n (ss j))),
      f (zs (j - 1)) ≤ f (zs (j - 1) + Pi.single (ss j) d)) :
    ∀ j, 2 ≤ j → j ≤ T - 1 → zs (j - 1) = zs j := by sorry

end TsengBCD.Stationary
