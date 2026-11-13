-- Prove2me | Theorems.Thm_SaglamGV_sMinus_bounds
-- name    : SaglamGV.sMinus_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:43.10959+00:00
-- url     : https://prove2.me/theorems/95c717d6-819f-4d8c-b970-beb388cc3208
-- title:
--   Bounds on $s(z)=\sinh z-z$
-- statement:
--   The function $s(z)=\sinh z-z$ satisfies
--
--   $$
--   s(z)\le0\ (z\le0),\qquad s(z)\le(\sinh1-1)z^3\ (0\le z\le1),\qquad s(z)\le\tfrac12e^z\ (z\ge1).
--   $$
--
--   Applied with $z=\tau\hat\mu(y)$ and $|\hat\mu|\le1$, these split $\mathbb E_y s(\tau\hat\mu(y))$ into a third-moment term and a tail term.
--
--   Differences from the source: none.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §3.3, p.4 (display s(z) ≤ 0 (z ≤ 0), s(z) ≤ (sinh 1 − 1)z³ (0 ≤ z ≤ 1), s(z) ≤ e^z/2 (z ≥ 1))

import Mathlib
import Definitions.Def_SaglamGV_Analytic

namespace SaglamGV

/-- Bounds on $s(z) = \sinh z − z$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §3.3, p.4: "We shall use s(z) ≤ 0 (z ≤ 0),
s(z) ≤ (sinh 1 − 1)z^3 (0 ≤ z ≤ 1), s(z) ≤ (1/2)e^z (z ≥ 1)"). -/
theorem sMinus_bounds :
    (∀ z : ℝ, z ≤ 0 → sMinus z ≤ 0) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 1 → sMinus z ≤ (Real.sinh 1 - 1) * z ^ 3) ∧
      (∀ z : ℝ, 1 ≤ z → sMinus z ≤ 1 / 2 * Real.exp z) := by sorry

end SaglamGV
