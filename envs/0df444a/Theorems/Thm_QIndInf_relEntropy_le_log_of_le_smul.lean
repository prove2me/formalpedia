-- Prove2me | Theorems.Thm_QIndInf_relEntropy_le_log_of_le_smul
-- name    : QIndInf.relEntropy_le_log_of_le_smul
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:16.557517+00:00
-- url     : https://prove2.me/theorems/cc9a06fc-28b1-4c28-9534-5d3106dd1764
-- title:
--   Eq. (73) — $D(\rho\|\sigma)\le\ln\lambda$ when $\rho\le\lambda\sigma$
-- statement:
--   Let $\rho$ and $\sigma$ be density operators on a finite-dimensional space and $\lambda>0$ a real number with $\rho\le\lambda\sigma$, that is, $\lambda\sigma-\rho$ positive semidefinite. Then
--
--   $$
--   D(\rho\|\sigma)\ \le\ \ln\lambda .
--   $$
--
--   In the proof of Theorem 4.2, $\rho=\rho_{\le m}$, $\sigma=\mu_{\le m}$ and $\lambda=2^{cs}$ by Eq. (58), giving $D(\rho_{\le m}\|\mu_{\le m})\le cs\ln2$, which is the paper's bound $cs$ (Eq. (73)) with $D$ in bits.
--
--   Differences from the source:
--   - generalization: ρ_{≤m}, μ_{≤m} with μ_{≤m} ≥ 2^{−cs} ρ_{≤m} → any density operators ρ, σ and any real λ > 0 with ρ ≤ λσ; reason: the paper's case is λ = 2^{cs}
--   - encoding: bound cs, D in bits → bound Real.log λ, D in nats; reason: with λ = 2^{cs}: ln λ = cs·ln 2, i.e. cs in bits; same inequality in another base
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (73), p.21, with Eq. (58), p.20

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

open scoped ComplexOrder

namespace QIndInf

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Relative entropy is at most the log of a domination constant** (Eq. (73)). If `ρ` and `σ`
are density operators and `ρ ≤ λ σ` for a real `λ > 0`, then `D(ρ‖σ) ≤ ln λ`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (73), p.21: `D(ρ_{≤m}‖μ_{≤m}) ≤ cs`, from
`μ_{≤m} ≥ 2^{−cs} ρ_{≤m}` (Eq. (58)), i.e. this statement with `λ = 2^{cs}`.

**Formalization Note.** `ρ ≤ λσ` is `(λσ − ρ).PosSemidef` (p.15). `D` is the published
`P21.relativeEntropy` in nats and the bound is the natural logarithm `Real.log λ` (its argument is
positive by hypothesis). With `λ = 2^{cs}` the bound is `cs · ln 2`, which is `cs` in bits, the
paper's Eq. (73). -/
theorem relEntropy_le_log_of_le_smul {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ)
    (lam : ℝ) (hlam : 0 < lam) (hdom : ((lam : ℂ) • σ - ρ).PosSemidef) :
    relativeEntropy ρ σ ≤ (Real.log lam : EReal) := by sorry

end QIndInf
