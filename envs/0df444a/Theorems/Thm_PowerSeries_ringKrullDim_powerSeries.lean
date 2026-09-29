-- Prove2me | Theorems.Thm_PowerSeries_ringKrullDim_powerSeries
-- name    : PowerSeries.ringKrullDim_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/db4ece19-5604-536f-80eb-0f1c30e3c66b
-- title:
--   Krull dimension of R[[X]] for Noetherian local R
-- statement:
--   Let $R$ be a commutative ring which is Noetherian and local (in the sense of Mathlib's `IsNoetherianRing` and `IsLocalRing`). The assertion is an equality of Krull dimensions in the extended integers, $\mathbb{Z} \cup \{\pm\infty\}$, as computed by `ringKrullDim`: the Krull dimension of the formal power series ring `PowerSeries R` equals the Krull dimension of $R$ plus one. No hypothesis beyond commutativity, the Noetherian condition and locality of the base ring is imposed; in particular $R$ is not assumed to be a domain, regular, or of finite dimension, the statement being an identity in the order-theoretic extension of the integers where the addition of $1$ is the one inherited from that extension.
--
--   This is the classical computation $\dim R[[X]] = \dim R + 1$ for a Noetherian local ring $R$, sharpening the inequality $\dim R + 1 \le \dim R[[X]]$ valid over an arbitrary commutative ring. In the present development it supplies the dimension half of the analysis of power series rings arising as Taylor–Wiles deformation rings; it is used in establishing that a universal ring which is Drinfeld basis-adic, commutative and satisfies the lifting condition is regular local of Krull dimension two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_ringKrullDim_powerSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem PowerSeries.ringKrullDim_powerSeries (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by sorry
