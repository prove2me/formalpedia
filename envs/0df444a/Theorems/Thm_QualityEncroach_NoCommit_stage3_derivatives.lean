-- Prove2me | Theorems.Thm_QualityEncroach_NoCommit_stage3_derivatives
-- name    : QualityEncroach.NoCommit.stage3_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:37.957371+00:00
-- url     : https://prove2.me/theorems/d6e32c7b-faf4-4362-93a4-ef9556b8879d
-- title:
--   Proof of Proposition 7, p. 37, (31)–(32) — ∂Π^HF_M/∂τ, ∂Π^LF_M/∂τ, their values at τ = 1, and q_M(1,q_R,u_R) > 0 ⇔ c + u_R(q_R + ku_R − 1) < 0
-- statement:
--   Let $k>0$, $c\ge0$, $u_R>0$ and let $q_R$, $w$ be arbitrary. Viewed as functions of $\tau>0$, the reduced profits $\Pi^{HF}_M(\tau,q_R,u_R,w)$ and $\Pi^{LF}_M(\tau,q_R,u_R,w)$ of the proof of Proposition 7 have derivatives
--   $$
--   \frac{\partial\Pi^{HF}_M}{\partial\tau} = -\frac{(c+u_R(q_R-3k\tau^2u_R+\tau))\,(c+u_R(q_R+\tau(k\tau u_R-1)))}{4\tau^2u_R},
--   $$
--   $$
--   \frac{\partial\Pi^{LF}_M}{\partial\tau} = -\frac{(c+\tau u_R(q_R+k\tau u_R-1))\,(c-\tau u_R(q_R+3k\tau u_R-1))}{4\tau^2u_R}.
--   $$
--   In particular, at $\tau=1$,
--   $$
--   \frac{\partial\Pi^{HF}_M}{\partial\tau}\Big|_{\tau=1} = -\frac{(c+u_R(q_R-3ku_R+1))(c+u_R(q_R+ku_R-1))}{4u_R},\qquad
--   \frac{\partial\Pi^{LF}_M}{\partial\tau}\Big|_{\tau=1} = -\frac{(c+u_R(q_R+ku_R-1))(c-u_R(q_R+3ku_R-1))}{4u_R}.
--   $$
--   Moreover, the optimal direct quantity at $\tau=1$ is positive exactly when $c+u_R(q_R+ku_R-1)<0$:
--   $$
--   q_M(1,q_R,u_R) = \Big(\frac{-c-q_Ru_R-ku_R^2+u_R}{2u_R}\Big)^{+} > 0 \iff c+u_R(q_R+ku_R-1)<0 .
--   $$
--
--   These are the expressions (31) and (32) and the encroachment condition from which the paper derives its contradiction.
--
--   **Formalization Note.** The page prints (31) as "$<0$" and (32) as "$>0$", as consequences of the optimality of $\tau=1$. This item states only the derivative values; the signs are not part of it, because optimality of $\tau=1$ yields only the weak inequalities $\le0$ and $\ge0$.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 37, proof of Proposition 7, ∂Π^HF_M/∂τ, ∂Π^LF_M/∂τ, (31), (32) and the encroachment condition

import Mathlib
import Definitions.Def_QualityEncroach_NoCommit_Game

namespace QualityEncroach.NoCommit

/-- Proof of Proposition 7, p. 37: the derivatives of `Π^HF_M` and `Π^LF_M` in `τ` at every
`τ > 0`, their values (31)–(32) at `τ = 1`, and the encroachment condition
`q_M(1, q_R, u_R) > 0 ⇔ c + u_R(q_R + k u_R − 1) < 0`. -/
theorem stage3_derivatives (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR : ℝ) (huR : 0 < uR) :
    (∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun s => PiHF k c s qR uR w)
        (-(c + uR * (qR - 3 * k * τ ^ 2 * uR + τ)) * (c + uR * (qR + τ * (k * τ * uR - 1)))
          / (4 * τ ^ 2 * uR)) τ) ∧
    (∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun s => PiLF k c s qR uR w)
        (-(c + τ * uR * (qR + k * τ * uR - 1)) * (c - τ * uR * (qR + 3 * k * τ * uR - 1))
          / (4 * τ ^ 2 * uR)) τ) ∧
    HasDerivAt (fun s => PiHF k c s qR uR w)
      (-(c + uR * (qR - 3 * k * uR + 1)) * (c + uR * (qR + k * uR - 1)) / (4 * uR)) 1 ∧
    HasDerivAt (fun s => PiLF k c s qR uR w)
      (-(c + uR * (qR + k * uR - 1)) * (c - uR * (qR + 3 * k * uR - 1)) / (4 * uR)) 1 ∧
    (0 < qMHF k c 1 qR uR ↔ c + uR * (qR + k * uR - 1) < 0) := by sorry

end QualityEncroach.NoCommit
