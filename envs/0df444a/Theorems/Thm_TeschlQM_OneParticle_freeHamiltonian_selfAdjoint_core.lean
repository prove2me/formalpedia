-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_freeHamiltonian_selfAdjoint_core
-- name    : TeschlQM.OneParticle.freeHamiltonian_selfAdjoint_core
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-10-07T15:20:40.691431+00:00
-- url     : https://prove2.me/theorems/5851bf86-00fe-4fb1-b055-816a6865ef9a
-- title:
--   Free Schrödinger operator: self-adjoint, $\sigma_{ess}(H_0)=[0,\infty)$, $C_c^\infty$ is a core
-- statement:
--   Let $n\ge 1$ and let $H_0=-\Delta$ be the free Schrödinger operator on $L^2(\mathbb R^n)$ with domain $H^2(\mathbb R^n)$, defined via the Fourier transform as multiplication by $(2\pi|\xi|)^2$. Then
--
--   1. $H_0$ is self-adjoint;
--   2. its essential spectrum is $\sigma_{ess}(H_0)=[0,\infty)$ (since $\sigma(H_0)=[0,\infty)$ and $H_0$ has no eigenvalues, the discrete spectrum is empty);
--   3. $C_c^\infty(\mathbb R^n)$ is a core for $H_0$.
--
--   This collects the facts about $H_0$ used in the proof of Theorem 10.2.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Theorem 7.8 (p. 168) and Lemma 7.9 (p. 168); used in the proof of Theorem 10.2, p. 222

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_testFunctions

namespace TeschlQM.OneParticle

/-- Teschl, Theorem 7.8 and Lemma 7.9 (pp. 167–168): for `n ≥ 1` the free Schrödinger operator
`H₀` is self-adjoint, its essential spectrum is `[0, ∞)`, and `C_c^∞(ℝⁿ)` is a core for `H₀`. -/
theorem freeHamiltonian_selfAdjoint_core (n : ℕ) (hn : 1 ≤ n) :
    IsSelfAdjoint (freeHamiltonian n) ∧
      essentialSpectrum (freeHamiltonian n) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 ∧
      (freeHamiltonian n).HasCore (testFunctions n) := by sorry

end TeschlQM.OneParticle
