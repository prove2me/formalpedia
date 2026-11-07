-- Prove2me | Theorems.Thm_QMAPlusGap_theorem_12
-- name    : QMAPlusGap.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:57.262209+00:00
-- url     : https://prove2.me/theorems/6027d216-e100-4ca9-a47e-b449e1f1e9cb
-- title:
--   Theorem 12 — dimension-independent Hilbert–Schmidt de Finetti theorem
-- statement:
--   Let $\Gamma_m$ be a density operator supported on $\mathrm{Sym}^m(\mathcal H)$ and $\rho_\ell$ its reduced state on $1\le\ell\le m$ registers. There is a probability measure $\mu$ on the unit sphere of $\mathcal H$ such that $\sigma_\ell=\int(|\psi\rangle\langle\psi|)^{\otimes\ell}d\mu(\psi)$ satisfies
--   $$
--   \|\rho_\ell-\sigma_\ell\|_2\ \le\ \sqrt{2(2^\ell-1)}\Big(\frac{3+2\ell(\ell-1)}{m}\Big)^{1/4}+\frac{8\ell+\sqrt\ell}{\sqrt m}.\tag{16}
--   $$
--   In particular, for every fixed $0<\eta<1/2$ there are $C\ge0$ and $k\in\mathbb N$ such that, for every finite-dimensional $\mathcal H$, every such $\Gamma_m$ and every $\ell$ with $1\le\ell\le(1/2-\eta)\log_2m$, one can choose $\sigma_\ell$ with
--   $$
--   \|\rho_\ell-\sigma_\ell\|_2\ \le\ C\,(1+\log m)^k\,m^{-\eta/2}.
--   $$
--   The bound is uniform in the local dimension $\dim\mathcal H$.
--
--   This is the paper's main technical result: a finite quantum de Finetti theorem in Hilbert–Schmidt norm for $\Theta(\log m)$ registers with no dependence on the local dimension.
--
--   Differences from the source:
--   - reading: poly(log m) m^{−η/2}, uniform in dim H → C (1 + log m)^k m^{−η/2} with C ≥ 0 and k depending only on η, chosen before the space ℂ^ι, m, ℓ and Γ; reason: 'uniform in the local dimension' fixes the order of the quantifiers; 1 + log m is a polynomial in log m for m ≥ 3
--   - encoding: a probability measure μ on the unit sphere of H → a probability measure on ℂ^ι concentrated on the unit sphere; reason: same objects
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Theorem 12, pp.25–26

import Mathlib
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_QMAPlusGap_IsSphereProb
import Definitions.Def_QMAPlusGap_tpMixture
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_hsNorm

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Theorem 12 (Dimension-independent approximation by tensor-power mixtures)**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), pp.25–26: "Let Γ_m be a
density operator supported on Sym^m(H), and let ρ_ℓ be its reduced state on 1 ≤ ℓ ≤ m registers. There is a
probability measure μ on the unit sphere of H such that σ_ℓ := ∫ (|ψ⟩⟨ψ|)^{⊗ℓ} dμ(ψ) satisfies
∥ρ_ℓ − σ_ℓ∥₂ ≤ √(2(2^ℓ − 1)) ((3 + 2ℓ(ℓ − 1))/m)^{1/4} + (8ℓ + √ℓ)/√m. (16) In particular, for every fixed
0 < η < 1/2, if ℓ ≤ (1/2 − η) log₂ m, then one can choose σ_ℓ so that ∥ρ_ℓ − σ_ℓ∥₂ ≤ poly(log m) m^{−η/2}. The
bound is uniform in the local dimension dim H."

Both clauses. In the second, `poly(log m)` is `C (1 + log m)^k` with `C`, `k` depending only on `η`, chosen
before the space `ℂ^ι`, `m`, `ℓ` and `Γ` (uniform in `dim H`).

**Formalization Note** `H = ℂ^ι` for any finite `ι`; `μ` is a probability measure on `ι → ℂ` concentrated on
the unit sphere; `∥·∥₂` is `WildeQIT.hsNorm`. -/
theorem theorem_12 :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ),
      WildeQIT.IsDensityOperator Γ → IsSymSupported Γ → 1 ≤ ℓ → ℓ ≤ m →
      ∃ μ : Measure (ι → ℂ), IsSphereProb μ ∧
        WildeQIT.hsNorm (reduce ℓ Γ - tpMixture ℓ μ) ≤
          Real.sqrt (2 * ((2 : ℝ) ^ ℓ - 1)) * ((3 + 2 * (ℓ : ℝ) * ((ℓ : ℝ) - 1)) / (m : ℝ)) ^ ((1 : ℝ) / 4) +
            (8 * (ℓ : ℝ) + Real.sqrt ℓ) / Real.sqrt m) ∧
    (∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m ℓ : ℕ) (Γ : Matrix (Fin m → ι) (Fin m → ι) ℂ),
        WildeQIT.IsDensityOperator Γ → IsSymSupported Γ → 1 ≤ ℓ →
        (ℓ : ℝ) ≤ (1 / 2 - η) * Real.logb 2 m →
        ∃ μ : Measure (ι → ℂ), IsSphereProb μ ∧
          WildeQIT.hsNorm (reduce ℓ Γ - tpMixture ℓ μ) ≤ C * (1 + Real.log m) ^ k * (m : ℝ) ^ (-(η / 2))) := by sorry

end QMAPlusGap
