-- Prove2me | Theorems.Thm_SYKCavity_Supplement_theorem_31
-- name    : SYKCavity.Supplement.theorem_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:49:00.771443+00:00
-- url     : https://prove2.me/theorems/fc6c73e7-a78e-42bf-aae5-51b2b528d7b4
-- title:
--   Theorem 31 — SK model at $\beta<1$: $\langle\sigma_A\rangle$ to $N^{-c}$ and $\log Z_N$ to $N^{-c}$ in $N^C$ bit operations
-- statement:
--   Consider the Sherrington–Kirkpatrick model $H_N(\sigma)=N^{-1/2}\sum_{i<j}J_{ij}\sigma_i\sigma_j$ on $\sigma\in\{-1,1\}^N$, with independent standard Gaussian couplings $J_{ij}$, $i<j$. Fix an inverse temperature $0\le\beta<1$, an observable degree $\ell\ge0$ and exponents $a,c>0$. Then there is a deterministic classical algorithm that outputs $\hat m_A(\beta,J)$ for every $|A|\le\ell$, and $\hat L(\beta,J)$, such that for all sufficiently large $N$
--   $$\Pr_J\Big[\sum_{|A|\le\ell}|\hat m_A-\langle\sigma_A\rangle_{\beta,J}|^2>N^{-2c}\ \text{ or }\ |\hat L-\log Z_N(\beta,J)|>N^{-c}\Big]\le N^{-a}.\qquad(8.4)$$
--   The number of bit operations is at most $N^C$, where $C$ depends only on the fixed parameters.
--
--   This covers the whole high-temperature phase $\beta<1$ of the SK model.
--
--   **Formalization Note** The SK model is the instance $P=\{2\}$, $\lambda_2=1$ of the mixture definitions. The algorithm is one deterministic program of the published log-cost rational RAM for all $N$. It reads $N$, an overflow flag, and $O(\log N)$-bit roundings of $\beta$, $\lambda_2$ and the couplings on a Gaussian box.
--
--   Differences from the source:
--   - encoding: the SK model: coupling J_ij/√N for each pair i < j, J_ij i.i.d. N(0,1) → the mixture skOrders = {2}, skCoeff = 1 of IsingModel (a_{2,N} = √(2!/(2N)) = N^{−1/2}), couplings indexed by 2-subsets of Fin N; reason: the same Hamiltonian; sites Fin N, spins Bool
--   - reading: a deterministic classical algorithm … The number of bit operations is at most N^C → one deterministic program (no coin instruction) of the published log-cost rational RAM BlottoFPTAS.Main.BitRAM for all N, halting on every input with bitCost ≤ N^C for every N ≥ 2; reason: bit complexity as App. M.6 proves it; C may absorb finitely many small N
--   - encoding: the input (β, J) and the finite-precision input of App. M.6 → bitInput: N, an overflow flag for max_e |J_e| > C₀⌈log₂(N+2)⌉, and the prec(N)-bit dyadic roundings of β, of λ_2 = 1 and of every coupling, prec(N) ≤ C_b⌈log₂(N+2)⌉, with C₀, C_b, prec chosen with the program; reason: M.6: 'The finite input consists of rounded entries on this box, with an overflow flag outside it', b = O(log N) bits; β is available through a certified approximation; the rounding of λ_2 = 1 is exact
--   - encoding: outputs m̂_A (|A| ≤ ℓ) and L̂; the event in (8.4) → the output decodes as #targets + 1 rationals (sets of size ≤ ℓ in a fixed order, then L̂); a non-decoding output counts as failure; the probability is the outer measure of the failure set under the exact Gaussian couplings, the targets at the exact J and β; reason: bit outputs; failure-on-garbage only strengthens the statement
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 31, p.67, (8.4); SK model p.66, (8.5) p.67; App. M.6, pp.178–180

import Mathlib
import Definitions.Def_SYKCavity_Supplement_IsingBitIO

open MeasureTheory

namespace SYKCavity.Supplement

open BlottoFPTAS.Main

/-- **Theorem 31 (SK thermal expectations and partition function)**, p.67 of A. Schmidhuber,
A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass transition*,
arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (8.4); SK model p.66, (8.5) p.67; bit model
App. M.6, pp.178–180.

Fix an inverse temperature `0 ≤ β < 1`, an observable degree `ℓ ≥ 0`, and exponents `a, c > 0`.
There is a deterministic classical algorithm that outputs `m̂_A(β, J)` for all `|A| ≤ ℓ` and
`L̂(β, J)` such that, for all sufficiently large `N`,
`Pr_J[Σ_{|A|≤ℓ} |m̂_A − ⟨σ_A⟩_{β,J}|² > N^{−2c} or |L̂ − log Z_N(β, J)| > N^{−c}] ≤ N^{−a}`.
The number of bit operations is at most `N^C`, where `C` depends only on the fixed parameters.

**Formalization Note.**
* The SK model `H_N(σ) = N^{−1/2} Σ_{i<j} J_ij σ_iσ_j`, `J_ij` i.i.d. `N(0,1)`, is the mixture
  `skOrders = {2}`, `skCoeff = 1` (`a_{2,N} = N^{−1/2}`).
* The algorithm is one deterministic `BitRAM` program for all `N`, run on `bitInput`: `N`, an
  overflow flag for `max_e |J_e| > C₀⌈log₂(N+2)⌉`, and the `prec N`-bit dyadic roundings of `β`,
  of `λ_2 = 1` and of the couplings, with `prec N ≤ C_b⌈log₂(N+2)⌉`. The program, `C`, `C_b`,
  `C₀` and `prec` are chosen after `(β, ℓ, a, c)` and before `N`.
* The bit cost is at most `N^C` and the run halts on every input, for every `N ≥ 2`; the failure
  probability (an output that does not decode counts as failure) is over the exact Gaussian
  couplings, with targets at the exact `J` and `β` (outer measure). -/
theorem theorem_31 (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ : ℕ) (a c : ℝ) (ha : 0 < a)
    (hc : 0 < c) :
    ∃ prog : BitRAM.Program, BitRAM.Deterministic prog ∧
      ∃ C Cb : ℕ, ∃ C₀ : ℝ, ∃ prec : ℕ → ℕ, (∀ N, prec N ≤ Cb * logLen N) ∧
        (∀ N : ℕ, 2 ≤ N → ∀ J : CIdx skOrders N → ℝ,
          BitRAM.Halts prog (bitInput skOrders skCoeff prec C₀ N β J) BitRAM.zeroTape ∧
            BitRAM.bitCost prog (bitInput skOrders skCoeff prec C₀ N β J) BitRAM.zeroTape ≤
              N ^ C) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          couplingLaw skOrders N {J | Fails skOrders skCoeff ℓ c prog prec C₀ N β J} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SYKCavity.Supplement
