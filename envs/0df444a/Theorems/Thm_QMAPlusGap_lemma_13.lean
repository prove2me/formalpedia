-- Prove2me | Theorems.Thm_QMAPlusGap_lemma_13
-- name    : QMAPlusGap.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:38.764263+00:00
-- url     : https://prove2.me/theorems/9a7a0381-af81-4e8e-9ac5-65f537f231ad
-- title:
--   Lemma 13 — removing the low-eigenvalue part
-- statement:
--   Let $\Gamma_m$ be a density operator supported on $\mathrm{Sym}^m(\mathcal H)$, fix $1\le\ell\le m$, let $\rho_1,\rho_\ell$ be its reduced states on one and $\ell$ registers, and let $P=\mathbf 1_{(1/m,1]}(\rho_1)$ be the projector onto the span of the eigenvectors of $\rho_1$ with eigenvalues larger than $1/m$. Then
--   $$
--   \big\|\rho_\ell-P^{\otimes\ell}\rho_\ell P^{\otimes\ell}\big\|_2\ \le\ \sqrt{2(2^\ell-1)}\Big(\frac{3+2\ell(\ell-1)}{m}\Big)^{1/4}.
--   $$
--
--   The part of $\rho_1$ below eigenvalue $1/m$ may have arbitrarily large rank, but in Hilbert–Schmidt norm it contributes only $O_\ell(m^{-1/4})$; this is where the dimension dependence of the de Finetti theorem is removed.
--
--   Differences from the source:
--   - encoding: P = 1_{(1/m,1]}(ρ₁) → highProj (reduceOne Γ) m, the functional calculus of the indicator of (1/m, ∞); reason: for a density operator the eigenvalues lie in [0, 1], so the two indicators agree
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 13, p.27 (restated p.32)

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_QMAPlusGap_highProj
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_hsNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Lemma 13 (Removing the low-eigenvalue part)**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.27 (restated p.32): "Let Γ_m be a density operator
supported on Sym^m(H). Fix 1 ≤ ℓ ≤ m, and let ρ_1 and ρ_ℓ be its reduced states on one and ℓ registers,
respectively. Let P = 1_{(1/m,1]}(ρ_1). Here, 1_{(1/m,1]}(ρ_1) denotes the orthogonal projector onto the span of the
eigenvectors of ρ_1 whose eigenvalues are larger than 1/m. Then
∥ρ_ℓ − P^{⊗ℓ} ρ_ℓ P^{⊗ℓ}∥₂ ≤ √(2(2^ℓ − 1)) ((3 + 2ℓ(ℓ − 1))/m)^{1/4}."

**Formalization Note** `P = highProj (reduceOne Γ) m`; `(·)^{1/4}` is `Real.rpow` of a nonnegative base. -/
theorem lemma_13 {ι : Type} [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ m)
    (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ) (hΓ : WildeQIT.IsDensityOperator Γ) (hΓs : IsSymSupported Γ) :
    WildeQIT.hsNorm (reduce ℓ Γ - WildeQIT.Schumacher.tensorPow ℓ (highProj (reduceOne Γ) m) * reduce ℓ Γ *
        WildeQIT.Schumacher.tensorPow ℓ (highProj (reduceOne Γ) m)) ≤
      Real.sqrt (2 * ((2 : ℝ) ^ ℓ - 1)) * ((3 + 2 * (ℓ : ℝ) * ((ℓ : ℝ) - 1)) / (m : ℝ)) ^ ((1 : ℝ) / 4) := by sorry

end QMAPlusGap
