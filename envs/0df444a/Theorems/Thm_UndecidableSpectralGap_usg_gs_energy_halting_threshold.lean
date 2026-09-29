-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gs_energy_halting_threshold
-- name    : UndecidableSpectralGap.usg_gs_energy_halting_threshold
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:01:15.876908+00:00
-- url     : https://prove2.me/theorems/821998eb-94f7-412e-957a-f5cbd41c0427
-- title:
--   Lemma 8 - relating the ground state energy to the halting problem (large lattices)
-- statement:
--   Let a machine be given, started on an initially blank tape. There is a family of translationally invariant nearest-neighbour Hamiltonians $\{H_u^{\Lambda(L)}\}_L$ on the 2D square lattice with open boundary conditions and some finite local Hilbert space dimension $d$, built from Hermitian row and column interactions and no on-site term, and there is a lattice size $L_1$ beyond which the following hold.
--
--   1. If $L \ge L_1$ and the machine has not halted after $L$ steps, then
--   $$\lambda_0\bigl(H_u^{\Lambda(L)}\bigr) = -2 ,$$
--   this ground state is non-degenerate, it is the only state of negative energy (every real spectral point below $0$ equals $-2$), and it is a product state $\bigotimes_{i \in \Lambda(L)} w_i$ over the sites, with each local vector $w_i$ non-zero.
--
--   2. If the machine halts, then there is a size $L_0$ — given by the halting time — such that $\lambda_0(H_u^{\Lambda(L)}) = 0$ for all $L > L_0$.
--
--   The Hamiltonian is the classical tiling Hamiltonian whose tiles encode the space-time diagram of the machine: as long as the computation has not halted, the special tile placed in the bottom-left corner picks up no penalty and contributes $-2$ to the energy, whereas after halting the tiling constraints can no longer be satisfied and the energy rises to $0$. This makes the ground state energy of a lattice model as hard to determine as the halting problem, and is the first step of the whole construction.
--
--   **Formalization notes.** Machines are represented by partial recursive codes: 'halts' means the evaluation on input $0$ (the blank tape) is defined, and 'has not halted after $L$ steps' means the step-bounded evaluation with bound $L$ returns nothing. The explicit bound $|S|(3|Q|+1)+2$ on the local dimension in terms of the alphabet $S$ and state set $Q$ of the machine is replaced here by the existence of a finite local dimension.
--
--   Two points distinguish this statement from the earlier formalization `UndecidableSpectralGap.usg_gs_energy_halting`, which was disproved. First, clause (i) is restricted to lattice sizes $L \ge L_1$: on $\Lambda(1)$ there are no nearest-neighbour pairs at all, so with no on-site term $H_u^{\Lambda(1)} = 0$ and its ground state energy is $0$, never $-2$; the tiling construction only makes sense once the lattice can host the corner tile and its neighbours. Second, 'product state' is taken in its usual sense of a product over the sites of the lattice, $\bigotimes_{i} w_i$ with site-dependent local vectors — in the construction the ground state is the computational basis state describing the space-time diagram of the computation, which is of this form, and not a state $v^{\otimes \Lambda(L)}$ with one and the same local vector at every site.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 2.2.1, p. 13, Lemma 8 (Relating ground state energy to the halting problem), parts (i)-(ii).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_gs_energy_halting_threshold (c : Nat.Partrec.Code) :
    ∃ (d : ℕ) (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (L1 : ℕ),
      hrow.IsHermitian ∧ hcol.IsHermitian ∧
      -- (i) for all large enough lattice sizes: if the machine has not halted after `L`
      -- steps, the ground state energy is `-2`, the ground state is non-degenerate, it is
      -- the unique state of negative energy, and it is a product state over the sites
      (∀ L ≥ L1, (Nat.Partrec.Code.evaln L c 0).isNone = true →
        gsEnergy (latticeHam L d 0 hrow hcol) = -2 ∧
        GroundStateNondegenerate (latticeHam L d 0 hrow hcol) ∧
        (∀ μ ∈ specReal (latticeHam L d 0 hrow hcol), μ < 0 → μ = -2) ∧
        ∃ w : Site L → (Fin d → ℂ), (∀ s, w s ≠ 0) ∧
          (latticeHam L d 0 hrow hcol).mulVec (fun cfg : Config L d => ∏ s, w s (cfg s))
            = (-2 : ℂ) • (fun cfg : Config L d => ∏ s, w s (cfg s))) ∧
      -- (ii) if the machine halts, then beyond the halting size the ground state energy is `0`
      ((c.eval 0).Dom → ∃ L0 : ℕ, ∀ L > L0, gsEnergy (latticeHam L d 0 hrow hcol) = 0) := by
  sorry

end UndecidableSpectralGap
