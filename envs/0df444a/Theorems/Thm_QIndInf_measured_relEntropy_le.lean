-- Prove2me | Theorems.Thm_QIndInf_measured_relEntropy_le
-- name    : QIndInf.measured_relEntropy_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:31.067532+00:00
-- url     : https://prove2.me/theorems/68856a3a-221b-4a88-807d-40241692e363
-- title:
--   Eq. (72) — measuring every register does not increase relative entropy
-- statement:
--   Let $\rho$ and $\sigma$ be states on $n$-qubit registers $R_1\cdots R_j$ and $\mathcal I_1,\dots,\mathcal I_j$ instruments. Then
--
--   $$
--   D\big((\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})\rho\,\big\|\,(\mathcal M_{\mathcal I_1}\otimes\cdots\otimes\mathcal M_{\mathcal I_j})\sigma\big)\ \le\ D(\rho\|\sigma).
--   $$
--
--   In the proof of Theorem 4.2 it is applied to $\rho_{\le m}$ and the reference $\mu_{\le m}$: $D(\omega^\rho_m\|\omega^\mu_m)\le D(\rho_{\le m}\|\mu_{\le m})$. When $\mathrm{supp}\,\rho\not\subseteq\mathrm{supp}\,\sigma$ the right side is $+\infty$.
--
--   Differences from the source:
--   - generalization: ρ_{≤m} and the reference μ_{≤m} → any two density operators on R₁⋯R_j; reason: the paper's pair consists of density operators
--   - encoding: relative entropy D in bits (log = log₂, p.14) → published P21.relativeEntropy in nats (EReal, +∞ off support); reason: the statement is homogeneous in the base of the logarithm: both sides scale by the same factor 1/ln 2
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (72), p.21; ω from Eq. (61), p.20

import Mathlib
import Definitions.Def_QIndInf_measAll
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

namespace QIndInf

open QAlgorithms.CopyMeasurements
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Measuring every register does not increase relative entropy** (Eq. (72)). For states
`ρ, σ` on `j` registers and instruments `I₁, …, I_j`,
`D((M_{I₁} ⊗ ⋯ ⊗ M_{I_j}) ρ ‖ (M_{I₁} ⊗ ⋯ ⊗ M_{I_j}) σ) ≤ D(ρ‖σ)`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eq. (72), p.21 (`D(ω^ρ_m‖ω^μ_m) ≤ D(ρ_{≤m}‖μ_{≤m})`),
with `ω` from Eq. (61), p.20.

**Formalization Note.** Stated for any two density operators on `R₁ … R_j`; the paper applies it
to `ρ_{≤m}` and the reference `μ_{≤m}`. `D` is the published `P21.relativeEntropy` (nats; the
inequality is homogeneous in the base), `+∞` when the support condition fails. -/
theorem measured_relEntropy_le {n j : ℕ} {k : Fin j → ℕ}
    (I : (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l)))
    (ρ σ : Matrix (Regs n j) (Regs n j) ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    relativeEntropy (measAll I ρ) (measAll I σ) ≤ relativeEntropy ρ σ := by sorry

end QIndInf
