-- Prove2me | Theorems.Thm_UpperHalfPlane_denom_eq_of_smul_eq_self
-- name    : UpperHalfPlane.denom_eq_of_smul_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/626bd2e7-adf0-5d66-a318-ae4f3ebe57a0
-- title:
--   Automorphy factor at a fixed point in H
-- statement:
--   Let $g \in \mathrm{GL}_2(\mathbb{R})$ satisfy $\det g = 1$ (as a unit of $\mathbb{R}$), let $\tau_0$ lie in the upper half plane $\mathfrak{H}$, and suppose $g$ fixes $\tau_0$ for the action of $\mathrm{GL}_2(\mathbb{R})$ on $\mathfrak{H}$. Write $\mathrm{denom}(g,\tau) = g_{10}\tau + g_{11}$ for the automorphy factor. Then five assertions hold simultaneously: (i) $\|\mathrm{denom}(g,\tau_0)\| = 1$; (ii) for every $\tau \in \mathfrak{H}$, $\big(g\tau - \overline{\tau_0}\big)\,\mathrm{denom}(g,\tau) = \big(\tau - \overline{\tau_0}\big)\,\mathrm{denom}(g,\tau_0)$, the bars denoting complex conjugation of the coordinates in $\mathbb{C}$; (iii) for every $\tau \in \mathfrak{H}$, $\big(g\tau - \tau_0\big)\,\mathrm{denom}(g,\tau)\,\mathrm{denom}(g,\tau_0) = \tau - \tau_0$; (iv) if $\mathrm{denom}(g,\tau_0) = 1$ then $g$ is the identity element of $\mathrm{GL}_2(\mathbb{R})$; and (v) for every $h \in \mathrm{GL}_2(\mathbb{R})$ with $\det h = 1$ and $h \cdot \tau_0 = \tau_0$, one has $\mathrm{denom}(gh,\tau_0) = \mathrm{denom}(g,\tau_0)\,\mathrm{denom}(h,\tau_0)$.
--
--   This collects the standard properties of the automorphy factor $j(g,\tau) = c\tau + d$ restricted to the stabiliser of a point $\tau_0 \in \mathfrak{H}$ inside the determinant-one part of $\mathrm{GL}_2(\mathbb{R})$: it takes values of modulus one, it linearises the action of $g$ in the Cayley coordinate centred at $\tau_0$, it is multiplicative on the stabiliser and it detects the identity, so that $g \mapsto j(g,\tau_0)$ is an injective character of that stabiliser. It is used in the construction of modular forms separating points and providing local parameters on modular curves, in [`ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_denom_eq_of_smul_eq_self.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem UpperHalfPlane.denom_eq_of_smul_eq_self
    (g : GL (Fin 2) ℝ) (hg : Matrix.GeneralLinearGroup.det g = 1) (τ₀ : ℍ) (hfix : g • τ₀ = τ₀) :
    ‖denom g τ₀‖ = 1 ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ = ((τ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ₀) ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (τ₀ : ℂ)) * denom g τ * denom g τ₀ = (τ : ℂ) - (τ₀ : ℂ)) ∧
    (denom g τ₀ = 1 → g = 1) ∧
    (∀ h : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.det h = 1 → h • τ₀ = τ₀ → denom (g * h) τ₀ = denom g τ₀ * denom h τ₀) := by sorry
