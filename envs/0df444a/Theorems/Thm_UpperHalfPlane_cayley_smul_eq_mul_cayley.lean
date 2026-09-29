-- Prove2me | Theorems.Thm_UpperHalfPlane_cayley_smul_eq_mul_cayley
-- name    : UpperHalfPlane.cayley_smul_eq_mul_cayley
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/76a81db3-7604-501a-8e21-459737ce652b
-- title:
--   Fixing τ₀ acts by a multiplier in the Cayley coordinate
-- statement:
--   Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, let $\tau_0$ be a point of the upper half-plane $\mathbb{H}$ fixed by $\gamma$ under Mathlib's Möbius action (that is, $\gamma \bullet \tau_0 = \tau_0$ as points of $\mathbb{H}$), and let $\tau \in \mathbb{H}$ be arbitrary. Write $c = \gamma_{10}$ and $d = \gamma_{11}$ for the bottom-row entries of $\gamma$, cast from $\mathbb{Z}$ into $\mathbb{C}$, and let $\bar\tau_0$ denote the image of $\tau_0$ under the complex conjugation ring endomorphism `starRingEnd ℂ`, all points of $\mathbb{H}$ being coerced to $\mathbb{C}$. The assertion is the identity of complex numbers $$\frac{\gamma\tau - \tau_0}{\gamma\tau - \bar\tau_0} = \frac{c\,\bar\tau_0 + d}{c\,\tau_0 + d}\cdot\frac{\tau - \tau_0}{\tau - \bar\tau_0},$$ i.e. in the Cayley coordinate $w(\tau) = (\tau-\tau_0)/(\tau-\bar\tau_0)$ centred at $\tau_0$, the transformation $\tau \mapsto \gamma\tau$ becomes multiplication by the constant $(c\bar\tau_0+d)/(c\tau_0+d)$. No nonvanishing hypotheses are imposed: the denominators occurring are automatically nonzero because $\tau, \tau_0$ lie in $\mathbb{H}$ and $\gamma$ has real entries.
--
--   This is the standard linearisation of the stabiliser of a point of $\mathbb{H}$ in the disc coordinate, as used in the classical discussion of elliptic points: the multiplier $(c\bar\tau_0+d)/(c\tau_0+d)$ has absolute value one, so the stabiliser acts by rotations about $\tau_0$. It is used in the analysis of sections of hyperplane bundles near such points, via [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_cayley_smul_eq_mul_cayley.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem UpperHalfPlane.cayley_smul_eq_mul_cayley (γ : SL(2, ℤ)) (τ₀ : ℍ) (h : γ • τ₀ = τ₀) (τ : ℍ) :
    ((↑(γ • τ) : ℂ) - τ₀) / ((↑(γ • τ) : ℂ) - (starRingEnd ℂ) τ₀)
      = (((γ 1 0 : ℤ) : ℂ) * (starRingEnd ℂ) τ₀ + ((γ 1 1 : ℤ) : ℂ))
        / (((γ 1 0 : ℤ) : ℂ) * τ₀ + ((γ 1 1 : ℤ) : ℂ))
        * (((τ : ℂ) - τ₀) / ((τ : ℂ) - (starRingEnd ℂ) τ₀)) := by sorry
