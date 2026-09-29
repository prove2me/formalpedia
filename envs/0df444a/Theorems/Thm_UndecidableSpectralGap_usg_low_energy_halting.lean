-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_low_energy_halting
-- name    : UndecidableSpectralGap.usg_low_energy_halting
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T04:47:53.082273+00:00
-- url     : https://prove2.me/theorems/9231416e-a460-4be8-92cb-30e472c12f00
-- title:
--   Theorem 9 - relating low energy properties to the halting problem
-- statement:
--   Let a machine be given, started on an initially blank tape, and let $\{H_q^{\Lambda(L)}\}_L$ be any family of translationally invariant nearest-neighbour Hamiltonians on square lattices with open boundary conditions, with Hermitian local terms on a $q$-dimensional local Hilbert space, whose ground state energy satisfies $\lambda_0(H_q^{\Lambda(L)})-eL^2\in[-\tfrac12,\tfrac12]$ for all $L$ and some constant $e$. Then there is a family $\{H^{\Lambda(L)}\}_L$ of translationally invariant nearest-neighbour Hamiltonians with Hermitian local terms on some finite local dimension $d$ such that:
--
--   1. if the machine has not halted after $L$ steps, then $H^{\Lambda(L)}$ has a non-degenerate ground state which is a product state $\bigotimes_{i\in\Lambda(L)}v$, and spectral gap $\Delta(H^{\Lambda(L)})\ge\tfrac12$;
--
--   2. if the machine halts, then there is a size $L_0$ such that for all $L>L_0$ the low-energy spectra agree with multiplicities in the window $[0,\tfrac12)$ above the respective ground state energies: for every $x\in[0,\tfrac12)$,
--
--   $$\dim\ker\bigl(H^{\Lambda(L)}-(\lambda_0(H^{\Lambda(L)})+x)\bigr)=\dim\ker\bigl(H_q^{\Lambda(L)}-(\lambda_0(H_q^{\Lambda(L)})+x)\bigr).$$
--
--   So in the halting case the constructed model reproduces, eigenvalue by eigenvalue and with the correct multiplicities, the low-energy physics of the given model, while in the non-halting case it is a trivial gapped system with a product ground state. Consequently *any* low-energy property that distinguishes a gapped system with product ground state from the low-energy sector of the given Hamiltonian - a spectral gap, topological order, decay of correlations - inherits the undecidability of the halting problem.
--
--   **Formalization note.** The identity of spectra as multisets is expressed as equality of eigenvalue multiplicities in the stated window; the isometry $V$ of the source, which implements this correspondence on eigenvectors, is not part of the statement. Machines are represented by partial recursive codes, with step-bounded evaluation standing for 'has not halted after $L$ steps', and the explicit local-dimension bound $d\le 2(q+1)+|S|(3|Q|+1)$ is replaced by the existence of a finite local dimension.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 2.2.2, pp. 13-14, Theorem 9 (Relating low energy properties to the halting problem), parts (i)-(iv).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_low_energy_halting (c : Nat.Partrec.Code) (q : ℕ)
    (hq1 : Matrix (Fin q) (Fin q) ℂ) (hqrow hqcol : Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ)
    (hq1H : hq1.IsHermitian) (hqrowH : hqrow.IsHermitian) (hqcolH : hqcol.IsHermitian)
    (e : ℝ)
    (hgs : ∀ L : ℕ, 0 < L →
      gsEnergy (latticeHam L q hq1 hqrow hqcol) - e * (L : ℝ) ^ 2 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    ∃ (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      h1.IsHermitian ∧ hrow.IsHermitian ∧ hcol.IsHermitian ∧
      -- (iii) if the machine has not halted after `L` steps, the Hamiltonian has a
      -- non-degenerate product ground state and spectral gap at least `1/2`
      (∀ L : ℕ, 0 < L → (Nat.Partrec.Code.evaln L c 0).isNone = true →
        GroundStateNondegenerate (latticeHam L d h1 hrow hcol) ∧
        HasGapAtLeast (latticeHam L d h1 hrow hcol) (1 / 2) ∧
        ∃ v : Fin d → ℂ, v ≠ 0 ∧
          (latticeHam L d h1 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, v (cfg s))
            = ((gsEnergy (latticeHam L d h1 hrow hcol) : ℝ) : ℂ) •
                (fun cfg : Config L d => ∏ s, v (cfg s))) ∧
      -- (iv) if the machine halts, then beyond the halting size the low-energy part of the
      -- spectrum of the new Hamiltonian agrees, with multiplicities, with that of the
      -- given Hamiltonian, in the window `[0, 1/2)` above the respective ground state energies
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, ∀ x ∈ Set.Ico (0 : ℝ) (1 / 2),
        eigMultiplicity (latticeHam L d h1 hrow hcol)
            (gsEnergy (latticeHam L d h1 hrow hcol) + x)
          = eigMultiplicity (latticeHam L q hq1 hqrow hqcol)
            (gsEnergy (latticeHam L q hq1 hqrow hqcol) + x)) := by
  sorry

end UndecidableSpectralGap
