-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_gap_unconstrained_dimension
-- name    : UndecidableSpectralGap.usg_gap_unconstrained_dimension
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:54:15.552889+00:00
-- url     : https://prove2.me/theorems/c1b3dedf-44da-40fd-848e-a8be34cc67be
-- title:
--   Corollary 7 - undecidability of the spectral gap for unconstrained dimension
-- statement:
--   Fix $\varepsilon>0$ and a universal machine. For every input $n$ there are a local Hilbert space dimension $D(n)$ - allowed to grow with $n$ - and Hermitian nearest-neighbour interactions $h_{\mathrm{row}}(n),h_{\mathrm{col}}(n)$ with **rational** matrix entries and operator norm smaller than $1+\varepsilon$, defining a family $\{H^{\Lambda(L)}(n)\}_L$ on square lattices with open boundary conditions and no on-site term, such that:
--
--   1. the family is frustration free: both interactions are positive semidefinite and $\lambda_0(H^{\Lambda(L)}(n))=0$ for every $L\ge1$;
--
--   2. if the machine halts on input $n$, the family is gapped with spectral gap at least $1$;
--
--   3. if it does not halt on input $n$, the family is gapless.
--
--   Since the halting problem is undecidable and the map $n\mapsto(h_{\mathrm{row}}(n),h_{\mathrm{col}}(n))$ is explicit, no algorithm can decide, on input a pair of rational interaction matrices, whether the associated family is gapped or gapless - even under the promise that one of the two holds, that the Hamiltonian is frustration free, and that in the gapped case the gap is at least $1$. The local dimension is unconstrained here; the difficulty of the main theorem is to obtain the same conclusion at a single fixed dimension.
--
--   **Formalization note.** The content is stated as the reduction from halting that the source's proof provides; the non-existence of a deciding algorithm then follows from undecidability of the halting problem. Machines are represented by partial recursive codes.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), pp. 1-102, doi:10.1017/fmp.2021.15, https://doi.org/10.1017/fmp.2021.15 (full version; same numbering as arXiv:1502.04573v5), Section 2.1, p. 10, Corollary 7 (Undecidability of the spectral gap for unconstrained dimension), together with Theorem 6 (i) (frustration-freeness), p. 9.

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

namespace UndecidableSpectralGap

theorem usg_gap_unconstrained_dimension (u : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ (D : ℕ → ℕ) (hrow hcol : ∀ n : ℕ,
        Matrix (Fin (D n) × Fin (D n)) (Fin (D n) × Fin (D n)) ℂ),
      ∀ n : ℕ,
        (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        -- rational matrix entries
        (∀ i j, ∃ r : ℚ, (hrow n) i j = (r : ℂ)) ∧
        (∀ i j, ∃ r : ℚ, (hcol n) i j = (r : ℂ)) ∧
        -- operator norms smaller than `1 + ε`
        opNorm (hrow n) < 1 + ε ∧ opNorm (hcol n) < 1 + ε ∧
        -- the family is frustration free (no on-site term is used)
        FrustrationFree (D n) 0 (hrow n) (hcol n) ∧
        -- halting gives a gapped system with gap at least 1
        ((u.eval n).Dom → GappedWithGap (D n) 0 (hrow n) (hcol n) 1) ∧
        -- non-halting gives a gapless system
        (¬ (u.eval n).Dom → Gapless (D n) 0 (hrow n) (hcol n)) := by
  sorry

end UndecidableSpectralGap
