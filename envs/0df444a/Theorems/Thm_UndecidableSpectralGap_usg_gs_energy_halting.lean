-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gs_energy_halting
-- name    : UndecidableSpectralGap.usg_gs_energy_halting
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T04:35:59.783662+00:00
-- url     : https://prove2.me/theorems/0ee3f955-20a7-49dd-bdb6-454c424eefee
-- title:
--   Lemma 8 - relating the ground state energy to the halting problem
-- statement:
--   Let a machine be given, started on an initially blank tape. There is a family of translationally invariant nearest-neighbour Hamiltonians $\{H_u^{\Lambda(L)}\}_L$ on the 2D square lattice with open boundary conditions and some finite local Hilbert space dimension $d$, built from Hermitian row and column interactions and no on-site term, such that:
--
--   1. if the machine has not halted after $L$ steps, then $\lambda_0(H_u^{\Lambda(L)})=-2$, this ground state is non-degenerate, it is the only state of negative energy (every eigenvalue below $0$ equals $-2$), and it is a **product state** $\bigotimes_{i\in\Lambda(L)}v$ for a single nonzero local vector $v$;
--
--   2. if the machine halts, then there is a size $L_0$ - given by the halting time - such that $\lambda_0(H_u^{\Lambda(L)})=0$ for all $L>L_0$.
--
--   The Hamiltonian is the classical tiling Hamiltonian whose tiles encode the space-time diagram of the machine: as long as the computation has not halted, an extra favourable tile can be placed and lowers the energy to $-2$, whereas after halting the tiling constraints can no longer be satisfied and the energy rises to $0$. This makes the ground state energy of a lattice model as hard to determine as the halting problem, and is the first step of the whole construction.
--
--   **Formalization note.** Machines are represented by partial recursive codes: 'halts' means the evaluation on input $0$ (the blank tape) is defined, and 'has not halted after $L$ steps' means the step-bounded evaluation with bound $L$ returns nothing. The explicit bound $|S|(3|Q|+1)+2$ on the local dimension in terms of the alphabet $S$ and state set $Q$ of the machine is replaced here by the existence of a finite local dimension.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 2.2.1, p. 13, Lemma 8 (Relating ground state energy to the halting problem), parts (i)-(ii).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_gs_energy_halting (c : Nat.Partrec.Code) :
    ∃ (d : ℕ) (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      hrow.IsHermitian ∧ hcol.IsHermitian ∧
      -- (i) if the machine has not halted after `L` steps, the ground state energy is `-2`,
      -- the ground state is a product state, and it is the unique state of negative energy
      (∀ L : ℕ, 0 < L → (Nat.Partrec.Code.evaln L c 0).isNone = true →
        gsEnergy (latticeHam L d 0 hrow hcol) = -2 ∧
        GroundStateNondegenerate (latticeHam L d 0 hrow hcol) ∧
        (∀ μ ∈ specReal (latticeHam L d 0 hrow hcol), μ < 0 → μ = -2) ∧
        ∃ v : Fin d → ℂ, v ≠ 0 ∧
          (latticeHam L d 0 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, v (cfg s))
            = (-2 : ℂ) • (fun cfg : Config L d => ∏ s, v (cfg s))) ∧
      -- (ii) if the machine halts, then beyond the halting size the ground state energy is `0`
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, gsEnergy (latticeHam L d 0 hrow hcol) = 0) := by
  sorry

end UndecidableSpectralGap
