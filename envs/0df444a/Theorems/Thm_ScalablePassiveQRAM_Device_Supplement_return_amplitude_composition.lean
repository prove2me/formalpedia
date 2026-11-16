-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_Supplement_return_amplitude_composition
-- name    : ScalablePassiveQRAM.Device.Supplement.return_amplitude_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:05:48.769707+00:00
-- url     : https://prove2.me/theorems/e93aac85-87ea-42f1-bb92-27ec2e9c3e4d
-- title:
--   Fact 12 — Return-amplitude composition
-- statement:
--   Let $a$ be the finite system of the algorithm's registers, and for $k=0,\dots,m$ let $e_k$ be the finite device-plus-environment system after $k$ queries. For $k=1,\dots,m$ let $V_k:\mathcal H_a\otimes\mathcal H_{e_{k-1}}\to\mathcal H_a\otimes\mathcal H_{e_k}$ be an isometry describing query $k$, including its environment. Let $|\xi_k\rangle\in\mathcal H_{e_k}$ be normalized idle states, and let $U_k$ be unitaries on $\mathcal H_a$ (the ideal queries). Define the return-amplitude operators
--
--   $$Z_k=(I\otimes\langle\xi_k|)\,V_k\,(I\otimes|\xi_{k-1}\rangle).$$
--
--   Let $\Phi_0,\dots,\Phi_m$ be arbitrary channels on the algorithm's registers. The physical channel starts the device and environment in $|\xi_0\rangle$, alternates $\Phi_{k-1}$ with query $V_k$, applies $\Phi_m$ and traces out $e_m$. The ideal channel is $\Phi_m\circ\mathrm{Ad}_{U_m}\circ\cdots\circ\mathrm{Ad}_{U_1}\circ\Phi_0$. If $\|Z_k-U_k\|\le r_k$ in operator norm for every $k$, then the diamond distance between the physical and ideal channels satisfies
--
--   $$\big\|\mathcal A^{\rm phys}-\mathcal A^{\rm ideal}\big\|_\diamond\le\min\Big\{2,\;4\Big(\sum_{k=1}^m\sqrt{r_k}\Big)^2\Big\}.$$
--
--   The bound charges each query only for how far its idle-to-idle block is from the ideal unitary, even though excitations may leave the idle state and later return. Theorem 11 applies it with $r_k=2B_k$.
--
--   **Formalization Note** Indices are zero-based in Lean: query $k+1$ is `V k`, `U k`, `r k`. The diamond distance is the base mission's `diamondDist`, the unhalved supremum over density operators on every finite reference times the algorithm's registers.
--
--   Differences from the source:
--   - encoding: queries, idle states, unitaries and bounds indexed $k=1,\dots,m$ and $\xi_0,\dots,\xi_m$ → zero-based families on ℕ (query $k+1$ is `V k`), with entries beyond $m$ unused; reason: same data, Lean index convention
--   - reading: the starting state of the device and environment is left implicit → the physical process starts the device and environment in $|\xi_0\rangle$; reason: $Z_1$ is defined by starting in $|\xi_0\rangle$ and the proof writes the initial joint state along it
--   - generalization: arbitrary channels between queries → also an arbitrary channel $\Phi_0$ before the first and $\Phi_m$ after the last query; reason: taking $\Phi_0$ and $\Phi_m$ to be the identity channel gives the source's statement
--   - encoding: final error as a diamond norm of the channel difference → the identical unhalved supremum over density operators on every finite reference, for explicitly composed maps; reason: same quantity, as in the base mission's error definitions
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Fact 12, eq. (83), p. 32 (proof p. 33). Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Supplement_ReturnAmplitude
import Definitions.Def_ScalablePassiveQRAM_Device_Static
import Mathlib

open scoped BigOperators Matrix
noncomputable section

namespace ScalablePassiveQRAM.Device.Supplement
open ScalablePassiveQRAM.Device

theorem return_amplitude_composition
    {a : Type} [Fintype a] [DecidableEq a]
    (env : ℕ → Type) [∀ k, Fintype (env k)] [∀ k, DecidableEq (env k)]
    (m : ℕ)
    (V : (k : ℕ) → Matrix (a × env (k+1)) (a × env k) ℂ)
    (ξ : (k : ℕ) → env k → ℂ)
    (U : ℕ → Matrix a a ℂ)
    (Φ : ℕ → WildeQIT.QChannel a a)
    (r : ℕ → ℝ)
    (hV : ∀ k < m, (V k)ᴴ * V k = 1)
    (hξ : ∀ k ≤ m, ∑ u, star (ξ k u) * ξ k u = 1)
    (hU : ∀ k < m, U k ∈ Matrix.unitaryGroup a ℂ)
    (hr : ∀ k < m, ScalablePassiveQRAM.Device.spectralNorm (returnAmplitude V ξ k - U k) ≤ r k) :
    diamondDist (physicalChannel V ξ Φ m) (idealChannel U Φ m) ≤
      min 2 (4 * (∑ k ∈ Finset.range m, Real.sqrt (r k)) ^ 2) := by sorry

end ScalablePassiveQRAM.Device.Supplement
