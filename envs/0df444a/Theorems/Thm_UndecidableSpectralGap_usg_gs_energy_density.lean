-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gs_energy_density
-- name    : UndecidableSpectralGap.usg_gs_energy_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T05:36:03.375207+00:00
-- url     : https://prove2.me/theorems/d775eef1-c239-4da2-997f-af0c859adb9a
-- title:
--   Theorem 5 - undecidability of the ground state energy density
-- statement:
--   Fix a universal machine. There are a fixed local Hilbert space dimension $d$ and, for every input $n$, Hermitian nearest-neighbour interactions $h_1(n),h_{\mathrm{row}}(n),h_{\mathrm{col}}(n)$ with algebraic (hence computable) matrix entries and local interaction strength at most $1$, such that the associated family $\{H^{\Lambda(L)}(n)\}_L$ on the square lattice with open boundary conditions has a well-defined ground state energy density
--
--   $$E_\rho(n)=\lim_{L\to\infty}\frac{\lambda_0(H^{\Lambda(L)}(n))}{L^2}\ \ge\ 0,$$
--
--   which satisfies $E_\rho(n)=0$ precisely when the machine does not halt on input $n$, and $E_\rho(n)>0$ precisely when it halts.
--
--   Since halting is undecidable, no algorithm decides whether $E_\rho=0$ or $E_\rho>0$ for a translationally invariant nearest-neighbour model on a 2D square lattice of fixed local dimension with computable matrix entries and bounded interaction strength. This is the undecidability of the ground state energy density, a result of independent interest that the source proves as a key intermediate step towards the spectral gap.
--
--   **Formalization note.** Machines are represented by partial recursive codes, and the halting of the machine on input $n$ is definedness of the evaluation at $n$.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 1.2, p. 4, Theorem 5 (Undecidability of g.s. energy density), restated in Section 6.1, p. 96.

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_gs_energy_density (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        -- algebraic matrix entries and local interaction strength bounded by 1
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j)) ∧
        localInteractionStrength (h1 n) (hrow n) (hcol n) ≤ 1) ∧
      ∀ n : ℕ, ∃ E : ℝ,
        HasGsEnergyDensity d (h1 n) (hrow n) (hcol n) E ∧ 0 ≤ E ∧
        (E = 0 ↔ ¬ (u.eval n).Dom) := by
  sorry

end UndecidableSpectralGap
