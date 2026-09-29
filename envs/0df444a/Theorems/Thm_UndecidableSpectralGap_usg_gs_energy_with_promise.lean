-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gs_energy_with_promise
-- name    : UndecidableSpectralGap.usg_gs_energy_with_promise
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T05:27:07.517368+00:00
-- url     : https://prove2.me/theorems/9db8c5d2-50ad-4dcf-97ae-5bc4b137f75e
-- title:
--   Corollary 54 - undecidability of the ground state energy with promise
-- statement:
--   Fix a universal machine. There are a fixed local Hilbert space dimension $d$, Hermitian interactions $h_1(n),h_{\mathrm{row}}(n),h_{\mathrm{col}}(n)$ with algebraic (hence computable) matrix entries and operator norm at most $\tfrac12$, and a threshold function $L(n)$, such that for every input $n$:
--
--   1. if the machine does not halt on $n$, then $\lambda_0(H_u^{\Lambda(L)}(n))\le0$ for every $L\ge1$;
--
--   2. if the machine halts on $n$, then $\lambda_0(H_u^{\Lambda(L)}(n))\ge1$ for every $L\ge L(n)$.
--
--   This is the promise version of the diverging-energy proposition: the two alternatives are separated by a constant gap in energy, $\le0$ against $\ge1$, rather than by an asymptotic rate. Deciding which of them holds is therefore as hard as the halting problem, and the constant separation is exactly the input required by the final step that converts an energy statement into a statement about the spectral gap. The threshold $L(n)$ is not computable from $n$.
--
--   **Formalization note.** Machines are represented by partial recursive codes, and the halting of the machine on input $n$ is definedness of the evaluation at $n$.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 6.1, p. 96, Corollary 54 (Undecidability of g.s. energy with promise).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_gs_energy_with_promise (u : Nat.Partrec.Code) :
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Lbound : ℕ → ℕ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j))) ∧
      ∀ n : ℕ,
        -- non-halting case: non-positive ground state energy at every size
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ 0) ∧
        -- halting case: ground state energy at least 1 from the size `Lbound n` on
        ((u.eval n).Dom → ∀ L ≥ Lbound n,
          1 ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n))) := by
  sorry

end UndecidableSpectralGap
