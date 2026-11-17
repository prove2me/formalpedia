-- Prove2me | Theorems.Thm_QDSGibbs_Supplement_theorem_4_2
-- name    : QDSGibbs.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:28:30.731317+00:00
-- url     : https://prove2.me/theorems/1a8ef8f9-1594-41b0-9c2f-04ec329cd43f
-- title:
--   Theorem 4.2 — classical DS contraction for finite-time QBP updates, $\Gamma\le-\kappa+2b\chi e^{-s_*T}$
-- statement:
--   Let $\Lambda\subset\mathbb Z^D$ be a finite lattice with spin space $[d]$ at every site and a bounded classical (product-basis diagonal) interaction of range $r$, and let $\pi\propto e^{-\beta H}$ be its Gibbs distribution, $\beta>0$. Let $\mathscr B$ be an $m$-fold covering of $\Lambda$ by nonempty labelled blocks (each site in exactly $m$ blocks), $b=\max_B|B|$, and suppose (4.6): for the heat-bath kernels $H_B$,
--   $$\Gamma_{\mathscr B}((H_B)_B)\le-\kappa,\qquad\kappa>0.$$
--   With $s_*$, $\omega_B$, $C_B$, $\chi$ as in the definitions, and $R_B(T)$ the diagonal restriction of the QBP block channel $e^{T\mathcal K_B}$:
--
--   1. $s_*\ge e^{-\beta\max_B\omega_B/2}\ge e^{-\beta\max_BC_B}$;
--   2. $\chi\le(2r+1)^D$;
--   3. for every $T\ge0$, $$\Gamma_{\mathscr B}((R_B(T))_B)\le-\kappa+2b\chi e^{-s_*T};\qquad(4.10)$$
--   4. if $T\ge s_*^{-1}\log(4b\chi/\kappa)$ (4.11), then $\Gamma_{\mathscr B}((R_B(T))_B)\le-\kappa/2$;
--   5. in a nearest-neighbour chain, $C_B\le2J_{\mathrm{int}}$ for every interval $B$, independently of its length.
--
--   The theorem replaces exact heat-bath updates by finite-time QBP block updates while keeping a classical Dobrushin–Shlosman contraction, with an explicit time $T$ depending only on $s_*$, $b$, $\chi$ and $\kappa$.
--
--   **Formalization Note** "$\Gamma\le b-a$" is `GammaLe R m a b` (no real subtraction). $W_H$ and $D^{\mathrm{diag}}$ are $[0,\infty]$-valued. Blocks are a labelled family counted with multiplicity.
--
--   Differences from the source:
--   - encoding: finite lattice Λ ⊂ ℤ^D (N sites), spin space [d] → sites Fin N placed by an injective pos : Fin N → ℤ^D, spin space Fin q with q ≥ 2; reason: the same finite subsets of ℤ^D; 2 ≤ d is the standing assumption of §2.1
--   - encoding: Γ_𝓑((R_B)_B) ≤ −κ + 2bχe^{−s_*T} (and ≤ −κ, ≤ −κ/2) → GammaLe: Σ_B D^diag_{R_B}(j) + mκ ≤ |𝓑| + m·2bχe^{−s_*T} in ℝ≥0∞ for every site j; reason: all terms are nonnegative, so this is the same inequality; it fails when some D^diag is infinite
--   - encoding: W_H, D^diag real (maxima of optimal transport costs) → ℝ≥0∞-valued infimum over couplings / supremum over pairs x ∼_j y; reason: equal on probability vectors; no junk value 0 when no coupling exists
--   - encoding: range r ≥ 1 (real), ℓ∞ distance → r : ℕ with 1 ≤ r, every support of ℓ∞-diameter ≤ r and 2 ≤ |X_α| (2.1); reason: lattice distances are integers, so diam ≤ r iff diam ≤ ⌊r⌋, and (2⌊r⌋+1)^D ≤ (2r+1)^D
--   - encoding: finite-time kernels R_B(T) → every T ≥ 0; reason: the evolution time of a semigroup is nonnegative
--   - encoding: a nonempty system (max over sites, factor 1/m) → hypotheses 1 ≤ N and 1 ≤ m; reason: excludes only the empty system, where Γ is undefined
--   - generalization: the nearest-neighbour chain of the setting (C_B ≤ 2J_int for intervals) → every nearest-neighbour chain Hamiltonian (IsChainHam, any local dimensions, quantum or classical); reason: the bound only uses that an interval has at most two crossing bonds and ‖W_b‖ ≤ J_int (p.11); the classical chain is a special case
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 4.2, pp.28–29 (setting §4.1 pp.25–27, (4.6) p.27)

import Mathlib
import Definitions.Def_QDSGibbs_Supplement_wH
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- **Theorem 4.2 (Classical DS contraction for finite-time QBP updates)** (Rouzé–Stilck França,
*Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions*, arXiv:2610.03578, held
file sha256 ede55815…, Theorem 4.2, pp.28–29). Setting of §4.1 (p.25): a finite lattice
`Λ ⊂ ℤ^D` (`N` sites placed injectively by `pos`), spin space `[q]` at every site, and a classical
(product-basis diagonal) interaction of range `r`. Let `𝓑` be an `m`-fold covering by nonempty blocks,
`b = max_B |B|`, and suppose (4.6): `Γ_𝓑((H_B)_B) ≤ −κ` with `κ > 0` for the heat-bath kernels. With
`s_*`, `ω_B`, `C_B`, `χ` as on p.28 and `R_B(T)` the diagonal restriction of `e^{T K_B}`:
1. `s_* ≥ e^{−β max_B ω_B/2} ≥ e^{−β max_B C_B}`;
2. `χ ≤ (2r + 1)^D`;
3. (4.10) `Γ_𝓑((R_B(T))_B) ≤ −κ + 2bχe^{−s_* T}` for every `T ≥ 0`;
4. (4.11) `T ≥ s_*^{−1} log(4bχ/κ)` implies `Γ_𝓑((R_B(T))_B) ≤ −κ/2`;
5. in a nearest-neighbour chain, `C_B ≤ 2J_int` for every interval `B`.

**Formalization Note**
* `Γ ≤ b − a` is `GammaLe R m a b` (no real subtraction; see its docstring). Blocks are a labelled
  family `blk : ι → Finset (Fin N)` (labels counted with multiplicity); `m`-fold covering means every
  site lies in exactly `m` labels.
* `R_B(T)` is `diagKernel`, the diagonal of the base `blockChannel β I B univ T`; the heat-bath kernel
  is `heatBath`. `max_B ω_B` and `max_B C_B` are real suprema over the finite label type.
* The lattice is `pos : Fin N → ℤ^D` injective with `ℓ∞` distance; range `r` means every support
  has `ℓ∞`-diameter at most `r` (and `2 ≤ |X_α|`, (2.1)). `N ≥ 1` and `m ≥ 1` exclude the empty
  system, where `max_j` and `1/m` are undefined.
* Clause 5 is stated for every nearest-neighbour chain Hamiltonian (`IsChainHam`, any local
  dimensions), `C_B = cB`. -/
theorem theorem_4_2 {N : ℕ} (hN : 1 ≤ N) (q : ℕ) (hq : 2 ≤ q) (D : ℕ)
    (pos : Fin N → (Fin D → ℤ)) (hpos : Function.Injective pos) (r : ℕ) (hr : 1 ≤ r)
    (I : Interaction (fun _ : Fin N => q)) (hI : I.IsValid) (hdiag : IsDiagonalInteraction I)
    (hrange : ∀ α, 2 ≤ (I.X α).card ∧
      ∀ i ∈ I.X α, ∀ j ∈ I.X α, ∀ k : Fin D, |pos i k - pos j k| ≤ (r : ℤ))
    (β : ℝ) (hβ : 0 < β) {ι : Type} [Fintype ι] (blk : ι → Finset (Fin N)) (m : ℕ) (hm : 1 ≤ m)
    (hblk : ∀ B, (blk B).Nonempty)
    (hcov : ∀ j : Fin N, (Finset.univ.filter fun B => j ∈ blk B).card = m)
    (κ : ℝ) (hκ : 0 < κ) (hDS : GammaLe (fun B => heatBath β I (blk B)) m κ 0) :
    (Real.exp (-β * (⨆ B, omegaB I (blk B)) / 2) ≤ sStar β I blk ∧
      Real.exp (-β * (⨆ B, cB I (blk B))) ≤ Real.exp (-β * (⨆ B, omegaB I (blk B)) / 2)) ∧
    chi I blk m ≤ (2 * (r : ℝ) + 1) ^ D ∧
    (∀ T : ℝ, 0 ≤ T →
      GammaLe (fun B => diagKernel β I (blk B) T) m κ
        (2 * (maxCard blk : ℝ) * chi I blk m * Real.exp (-(sStar β I blk) * T))) ∧
    (∀ T : ℝ, 0 ≤ T →
      (sStar β I blk)⁻¹ * Real.log (4 * (maxCard blk : ℝ) * chi I blk m / κ) ≤ T →
      GammaLe (fun B => diagKernel β I (blk B) T) m (κ / 2) 0) ∧
    (∀ (N' : ℕ) (d' : Fin N' → ℕ) (V : Fin N' → Op d') (W : Fin (N' - 1) → Op d'),
      IsChainHam V W → ∀ B : Finset (Fin N'), IsInterval B →
        cB (chain V W) B ≤ 2 * jint (chain V W)) := by sorry

end QDSGibbs.Supplement
