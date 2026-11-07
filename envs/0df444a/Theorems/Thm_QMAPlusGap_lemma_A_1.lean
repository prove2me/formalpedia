-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_A_1
-- name    : QMAPlusGap.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:23.709185+00:00
-- url     : https://prove2.me/theorems/eff190d1-4f32-4d3c-8e77-b7ca4eefdf74
-- title:
--   Lemma A.1 — two-copy swap expectations equal $\operatorname{Tr}(\rho_\ell B\rho_\ell B)$
-- statement:
--   Let $\Gamma_m$ be a density operator supported on $\mathrm{Sym}^m(\mathcal H)$ and $\rho_\ell$ its reduced state on $\ell$ registers, $1\le\ell\le m$. Let $B_1,\dots,B_\ell$ be operators on $\mathcal H$ and $B=B_1\otimes\cdots\otimes B_\ell$. If $i=(i_1,\dots,i_\ell)$ and $j=(j_1,\dots,j_\ell)$ are lists of pairwise distinct positions in $[m]$, then
--   $$
--   \operatorname{Tr}\Big[(\Gamma_m\otimes\Gamma_m)\prod_{r=1}^{\ell}(B_r)^{(1)}_{i_r}(B_r)^{(2)}_{j_r}F_{i_rj_r}\Big]=\operatorname{Tr}(\rho_\ell B\rho_\ell B).\tag{A.2}
--   $$
--
--   It turns Hilbert–Schmidt quantities of reduced states into expectations of swap operators on two copies of $\Gamma_m$, the basic tool of the proof of Lemma 13.
--
--   Differences from the source:
--   - encoding: the product Π_{r=1}^{ℓ} of the factors → the product in the order r = 0, 1, …, ℓ − 1 (List.ofFn); reason: factors for different r act on disjoint registers and commute
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma A.1, p.32

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily
import Definitions.Def_QMAPlusGap_onFirst
import Definitions.Def_QMAPlusGap_swapF
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma A.1**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.32: "Let Γ_m be a density operator supported on Sym^m(H), and let ρ_ℓ be its reduced
state on ℓ registers, where 1 ≤ ℓ ≤ m. Let B_1, …, B_ℓ be operators on H and set B = B_1 ⊗ ⋯ ⊗ B_ℓ. If
i = (i_1, …, i_ℓ) and j = (j_1, …, j_ℓ) are lists of pairwise distinct positions in [m], then
Tr[(Γ_m ⊗ Γ_m) Π_{r=1}^{ℓ} (B_r)^{(1)}_{i_r} (B_r)^{(2)}_{j_r} F_{i_r j_r}] = Tr(ρ_ℓ B ρ_ℓ B). (A.2)"

**Formalization Note** Positions are `0`-based; the lists are injective maps `Fin ℓ → Fin m`. The factors for
different `r` act on disjoint registers and commute, so the product is taken in the order `r = 0, 1, …`
(`List.ofFn`). `Γ_m ⊗ Γ_m` is the Kronecker product on two copies. -/
theorem lemma_A_1 {ι : Type} [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ m)
    (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ) (hΓ : WildeQIT.IsDensityOperator Γ) (hΓs : IsSymSupported Γ)
    (Bs : Fin ℓ → Matrix ι ι ℂ) (i j : Fin ℓ → Fin m) (hi : Function.Injective i)
    (hj : Function.Injective j) :
    Matrix.trace (Matrix.kroneckerMap (· * ·) Γ Γ *
        (List.ofFn fun r : Fin ℓ => onFirst (i r) (Bs r) * onSecond (j r) (Bs r) * swapF (i r) (j r)).prod) =
      Matrix.trace (reduce ℓ Γ * OptimalSpectrum.Entangled.kronFamily Bs * reduce ℓ Γ * OptimalSpectrum.Entangled.kronFamily Bs) := by sorry

end QMAPlusGap
