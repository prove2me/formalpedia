-- Prove2me | Theorems.Thm_WildeQIT_Recover_theorem_12_5_1
-- name    : WildeQIT.Recover.theorem_12_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:22:35.675135+00:00
-- url     : https://prove2.me/theorems/90c5fb4a-20ae-48f5-bedc-7b9dbce2e052
-- title:
--   Theorem 12.5.1 — $D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))\ge-\int\beta_0(t)\log F(\rho,(\mathcal R^{t/2}_{\sigma,\mathcal N}\circ\mathcal N)(\rho))\,dt$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space $\mathcal H$ with $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$, and let $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ be a quantum channel. Then
--
--   $$
--   D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))\ \ge\ -\int_{-\infty}^{\infty}dt\ \beta_0(t)\,\log F\!\left(\rho,(\mathcal R^{t/2}_{\sigma,\mathcal N}\circ\mathcal N)(\rho)\right),
--   $$
--
--   where $\beta_0(t)=\frac{\pi}{2}[\cosh(\pi t)+1]^{-1}$ is a probability density on $\mathbb R$, $\mathcal R^{t/2}_{\sigma,\mathcal N}$ is the rotated Petz map, $F(\rho,\omega)=\|\sqrt\rho\sqrt\omega\|_1^2$ is the fidelity, $D$ is the quantum relative entropy and $\log$ is the binary logarithm.
--
--   The relative entropy can only decrease under a channel; this theorem quantifies the decrease: if it is small, then on average over $t$ the rotated Petz maps nearly recover $\rho$ from $\mathcal N(\rho)$, while each of them recovers $\sigma$ exactly. It implies the recoverability theorem 12.1.1, the monotonicity of quantum relative entropy, and the refinements of strong subadditivity, of concavity of conditional entropy and of joint convexity in §12.6.
--
--   **Formalization Note** The right side is the Lebesgue integral of the nonnegative integrand $\beta_0(t)\,(-\log_2F)$ with values in $[0,+\infty]$, where $-\log_2 0=+\infty$; no default value for a non-integrable function occurs. $\beta_0$ is the published `betaZero` of the Junge–Renner–Sutter–Wilde–Winter formalization. Relative entropies are extended reals; under the hypotheses both are finite, so the difference on the left is the book's real number.
--
--   Differences from the source:
--   - encoding: $-\int\beta_0(t)\log F\,dt$ → $\int^{-}\beta_0(t)\,\bigl(-\log_2F\bigr)\,dt$ as a lower Lebesgue integral in $[0,+\infty]$ with $-\log_2 0=+\infty$; reason: the integrand is nonnegative ($F\le1$, (12.3)), so the two integrals coincide, including the value $+\infty$.
--   - encoding: $D$ real or $+\infty$ → $D$ in the extended reals; reason: same values, and both relative entropies are finite under the hypotheses.
--   - encoding: a quantum channel → a channel in Choi–Kraus form; reason: every channel has a finite Kraus form (Theorem 4.4.1).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.5.1, (12.103), p. 378; Definition 12.1.1, p. 365

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_Recover_negLog2
import Definitions.Def_WildeQIT_Recover_rotatedPetz
open scoped ComplexOrder
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P21 (betaZero)

namespace WildeQIT.Recover

/-- **Theorem 12.5.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Theorem 12.5.1, (12.103), p. 378). Let `ρ` be a density operator, `σ` positive semi-definite with
`supp(ρ) ⊆ supp(σ)`, and `𝒩` a quantum channel (Definition 12.1.1). Then
`D(ρ‖σ) − D(𝒩(ρ)‖𝒩(σ)) ≥ −∫ dt β₀(t) log F(ρ, (ℛ^{t/2}_{σ,𝒩} ∘ 𝒩)(ρ))`,
with `β₀(t) = (π/2)[cosh(πt) + 1]⁻¹`.

**Formalization Note** Finite dimensions; `log` is base 2. `D` is `EReal`-valued
(Definition 11.8.2). The right side is the lower Lebesgue integral of the `[0, +∞]`-valued
integrand `β₀(t) · (−log₂ F)`, with `−log₂ 0 = +∞`, so no Bochner default value occurs. `β₀` is
`betaZero` of the published definitions of Junge–Renner–Sutter–Wilde–Winter (2018). -/
theorem theorem_12_5_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    qRelEntropy ρ σ - qRelEntropy (N.apply ρ) (N.apply σ) ≥
      (((∫⁻ t : ℝ, ENNReal.ofReal (betaZero t) *
          negLog2 (fidelity ρ (rotatedPetz σ N (t / 2) (N.apply ρ)))) : ℝ≥0∞) : EReal) := by sorry

end WildeQIT.Recover
