-- Prove2me | Theorems.Thm_ReflectionlessPotential_parity_spectral_weight
-- name    : ReflectionlessPotential.parity_spectral_weight
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:58:16.675876+00:00
-- url     : https://prove2.me/theorems/bc2598f5-339d-4045-8887-fcf599657e28
-- title:
--   The parity basis on $k>0$ carries the same spectral weight as $\psi_k$ on $k\in\mathbb{R}$
-- statement:
--   Equation (5.12) compared with (4.9): the even/odd parity continuum states, integrated over the half line $k>0$, carry exactly the same spectral weight as the states $\psi_{k}$ integrated over the whole line.
--
--   For $\kappa>0$ and continuous compactly supported $f$,
--   $$\int_{0}^{\infty}\Bigl(\bigl\lvert\langle\psi^{e}_{k},f\rangle\bigr\rvert^{2}+\bigl\lvert\langle\psi^{o}_{k},f\rangle\bigr\rvert^{2}\Bigr)dk
--   \;=\;\int_{-\infty}^{\infty}\bigl\lvert\langle\psi_{k},f\rangle\bigr\rvert^{2}\,dk ,$$
--   where $\langle g, f\rangle = \int \overline{g(x)}f(x)\,dx$. The reason is that for $k>0$ the pair $(\psi^{e}_{k},\psi^{o}_{k})$ is a unitary recombination of the pair $(\psi_{k},\psi_{-k})$: parity maps $\psi_{k}$ to a unimodular multiple of $\psi_{-k}$. Consequently the two computations of the continuum contribution to the completeness relation must agree, as the paper finds.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem parity_spectral_weight (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    (∫ k in Set.Ioi (0 : ℝ), (‖coeffEven κ k f‖ ^ 2 + ‖coeffOdd κ k f‖ ^ 2)) =
      ∫ k : ℝ, ‖coeffC κ k f‖ ^ 2 := by sorry

end ReflectionlessPotential
