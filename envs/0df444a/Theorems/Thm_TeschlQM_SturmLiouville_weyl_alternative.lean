-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_weyl_alternative
-- name    : TeschlQM.SturmLiouville.weyl_alternative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:49:24.005911+00:00
-- url     : https://prove2.me/theorems/0bcf995e-7880-441e-919c-ae0f7aeb78b2
-- title:
--   Theorem 9.9 — Weyl's limit circle / limit point alternative
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data on $I = (a,b)$ and let $\tau f = \frac{1}{r}(-(pf')' + qf)$. Then:
--
--   1. $\tau$ is limit circle at $a$ if and only if for one $z_0 \in \mathbb{C}$ all solutions of $(\tau - z_0)u = 0$ are square integrable near $a$;
--   2. if $\tau$ is limit circle at $a$, then for all $z \in \mathbb{C}$ all solutions of $(\tau - z)u = 0$ are square integrable near $a$;
--   3. and similarly for $b$.
--
--   $$\tau \text{ l.c. at } a \iff \exists z_0 \in \mathbb{C}\ \forall u:\ (\tau - z_0)u = 0 \Rightarrow u \in L^2((a,c), r\,dx) \text{ for some } c \in I.$$
--
--   Limit circle is defined through boundary Wronskians on the maximal domain $\mathfrak{D}(\tau)$ (p. 187), so the theorem converts a statement about boundary conditions of self-adjoint realizations into a statement about the solutions of an ordinary differential equation, which can be checked in examples.
--
--   **Formalization Note.** Solutions are complex-valued with $u, pu' \in AC_{loc}(I)$; the coefficients are only locally integrable. "Square integrable near $a$" is `IsSqIntegrableNearLeft` (some $c \in I$, weight $r$).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 191, Theorem 9.9

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

/-- Teschl, Theorem 9.9 (Weyl alternative), p. 191. `τ` is l.c. at `a` if and only if for one
`z₀ ∈ ℂ` all solutions of `(τ − z₀) u = 0` are square integrable near `a`. This then holds for all
`z ∈ ℂ`, and similarly for `b`. Limit circle is the Wronskian notion of p. 187, not square
integrability. -/
theorem weyl_alternative (L : SLData) :
    (IsLimitCircleLeft L ↔
        ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) ∧
      (IsLimitCircleLeft L →
        ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
      (IsLimitCircleRight L ↔
        ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) ∧
      (IsLimitCircleRight L →
        ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) := by sorry

end TeschlQM.SturmLiouville
