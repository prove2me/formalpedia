-- Prove2me | Theorems.Thm_ReflectionlessPotential_psiEven_psiOdd_eq
-- name    : ReflectionlessPotential.psiEven_psiOdd_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:57:47.786058+00:00
-- url     : https://prove2.me/theorems/7dd210ac-bca3-4f2c-8338-7f5210845db8
-- title:
--   Closed forms of the parity eigenstates $\psi_k^e$, $\psi_k^o$
-- statement:
--   Equations (5.1) and (5.2): the parity eigenstates of the reflectionless potential.
--
--   The Hamiltonian commutes with the parity operator $(\Pi\psi)(x) = \psi(-x)$, so the continuum states can be symmetrized. With $\psi^{e}_{k} = \tfrac{1}{\sqrt2}\bigl(\psi_{k}(x)+\psi_{k}(-x)\bigr)$ and $\psi^{o}_{k} = \tfrac{1}{\sqrt2}\bigl(\psi_{k}(x)-\psi_{k}(-x)\bigr)$ one has, for $\kappa>0$ and all real $k, x$,
--   $$\psi^{e}_{k}(x) \;=\; \frac{1}{\sqrt{\pi}}\,\frac{k\cos kx - \kappa \sin kx \,\tanh \kappa x}{\kappa + ik},
--   \qquad
--   \psi^{o}_{k}(x) \;=\; \frac{i}{\sqrt{\pi}}\,\frac{k\sin kx + \kappa\cos kx\,\tanh\kappa x}{\kappa+ik}.$$
--   These are simultaneous eigenstates of $H$ and of $\Pi$, with parity $+1$ and $-1$ respectively.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psiEven_psiOdd_eq (κ k x : ℝ) (hκ : 0 < κ) :
    psiEven κ k x =
        ((k * Real.cos (k * x) - κ * Real.sin (k * x) * Real.tanh (κ * x) : ℝ) : ℂ) /
          ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k)) ∧
      psiOdd κ k x =
        Complex.I * ((k * Real.sin (k * x) + κ * Real.cos (k * x) * Real.tanh (κ * x) : ℝ) : ℂ) /
          ((Real.sqrt Real.pi : ℂ) * ((κ : ℂ) + Complex.I * k)) := by sorry

end ReflectionlessPotential
