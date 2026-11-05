-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_theorem_7
-- name    : ShallowShadows.ShadowNorm.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:54.087099+00:00
-- url     : https://prove2.me/theorems/eba5b6c8-7624-4fac-b08b-ddfe7c3f168c
-- title:
--   Theorem 7: $\|O\|^2_{s(d),\sigma}=\|O\|^2_{s(d),\mathrm{LS}}+\operatorname{tr}(\sigma\tilde O)$ with $\|O\|^2_{s(d),\mathrm{LS}}=\sum_\lambda\beta_\lambda^2/t_{\lambda,d}$, at every depth $d$
-- statement:
--   Let $n = 2m$ qubits and a depth $d \in \{\infty, 0, 1, 2, \dots\}$, with $\mathcal U_d$ the shallow-shadow ensemble, $\mathcal M_d$ its measurement channel, $t_{\lambda,d}$ and $\tau_{(\lambda,\lambda'),d}$ the probabilities of Eqs. (5) and (19). For any observable $O$ with Pauli decomposition $O = \sum_\lambda \beta_\lambda P^\lambda$ and any state $\sigma$, the square of the state dependent shadow norm
--
--   $$
--   \|O\|^2_{s(d),\sigma} = \mathbb E_{U\sim\mathcal U_d}\Big[\sum_{b\in\{0,1\}^n}\langle b|U\sigma U^\dagger|b\rangle\langle b|U\mathcal M_d^{-1}(O)U^\dagger|b\rangle^2\Big]
--   $$
--
--   is given by
--
--   $$
--   \|O\|^2_{s(d),\sigma} = \operatorname{tr}\Big(\sigma\sum_{\lambda,\lambda'}\beta_\lambda\beta_{\lambda'}\frac{\tau_{(\lambda,\lambda'),d}}{t_{\lambda,d}t_{\lambda',d}}P^\lambda P^{\lambda'}\Big) = \|O\|^2_{s(d),\mathrm{LS}} + \operatorname{tr}(\sigma\tilde O),
--   $$
--
--   with $\tilde O$ of Eq. (21) and $\|O\|^2_{s(d),\mathrm{LS}} = \mathbb E_{\sigma\sim\mathcal E}[\|O\|^2_{s(d),\sigma}]$ for any state one-design $\mathcal E$. Furthermore,
--
--   $$
--   \|O\|^2_{s(d),\mathrm{LS}} = \sum_{\lambda\in\{0,1\}^{2n}}\frac{\beta_\lambda^2}{t_{\lambda,d}}.
--   $$
--
--   The theorem gives the exact sample-complexity parameter of shallow classical shadows at every depth: a state independent part computable from the eigenvalues $t_{\lambda,d}$ alone, plus a correction $\operatorname{tr}(\sigma\tilde O)$ governed by $\tau$.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
--   - reading: any observable O → any Hermitian matrix O (O.IsHermitian); reason: an observable is a Hermitian operator, as in the HKP setting the paper builds on
--   - encoding: M^{-1}, the inverse of the measurement channel M_d → ClassicalShadow.Linear.measChannelInv = Ring.inverse (measChannel E); reason: Ring.inverse is the inverse whenever M_d is a unit, which holds for every U_d (Eq. (11), milestone)
--   - generalization: any ensemble of states E with E_{σ∼E}[σ] = I/2^n → any probability measure 𝓔 on density operators with entrywise mean ∫ σ_ab d𝓔 = 2^{-n} δ_ab (IsStateOneDesign); reason: every finite ensemble of states is such a measure, so the statement specializes to the source's ensembles; the entrywise mean is the matrix identity E[σ] = I/2^n
--   - encoding: real identities → identities in ℂ, real quantities cast to ℂ; β_λ = 2^{-n} tr(P^λ O) complex-valued; reason: β is real for Hermitian O; working in ℂ drops no imaginary part
--   - encoding: O = Σ_λ β_λ P^λ → β_λ := 2^{-n} tr(P^λ O) (coeff); reason: tr(P^λ P^λ') = 2^n δ_λλ' makes the Pauli decomposition of every O unique, with these coefficients
--   - encoding: E_{U∼U_d}[Σ_b ⟨b|UσU†|b⟩ ⟨b|UM^{-1}(O)U†|b⟩²] → stateShadowNormSq, the finite weighted sum with the real part of the Born weight and of the square; reason: for a density operator σ, a Hermitian O and every U_d both numbers are real, since M_d^{-1}(O) = Σ_λ (β_λ/t_λ,d) P^λ is Hermitian by Eq. (11), so the real parts change nothing
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Theorem 7, Eqs. (20)–(22), p. 7 (proof Appendix F, p. 19)

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_lsShadowNormSq
import Definitions.Def_ShallowShadows_ShadowNorm_oTilde

open ClassicalShadow.Linear MeasureTheory

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Theorem 7,
Eqs. (20)–(22), p. 7 (proof Appendix F, p. 19). For any observable `O` with Pauli decomposition
`O = Σ_λ β_λ P^λ` and any state `σ`,
`‖O‖²_{s(d),σ} = tr(σ Σ_{λ,λ'} β_λ β_λ' τ_{(λ,λ'),d} / (t_{λ,d} t_{λ',d}) P^λ P^λ')
= ‖O‖²_{s(d),LS} + tr(σ Õ)` (20), with `Õ` of Eq. (21), and
`‖O‖²_{s(d),LS} = Σ_λ β_λ² / t_{λ,d}` (22).

Stated for every `m` (`n = 2m` qubits) and every depth `d ∈ {∞, 0, 1, 2, …}`: the first block of
three clauses is the brickwork ensemble `𝒰_k` for every `k ∈ ℕ`, the second block the global
Clifford ensemble `𝒰_∞`. In each block: (1) the first equality of (20) for every Hermitian `O` and
every density operator `σ`; (2) the second equality of (20) for every state one-design `ℰ`
defining `‖O‖²_{s(d),LS}` (Eq. (18)); (3) Eq. (22) for every state one-design `ℰ`.

**Formalization Note.** `‖O‖²_{s(d),σ}` is `stateShadowNormSq` (the display on p. 7, with `M_d⁻¹`
the inverse of the channel of Eq. (2)); `‖O‖²_{s(d),LS}` is `lsShadowNormSq` (Eq. (18));
`t` and `τ` are the probabilities of Eqs. (5) and (19); `β_λ = 2^{-n} tr(P^λ O)`. Observables are
Hermitian matrices; state one-designs are probability measures on density operators with mean
`𝕀/2ⁿ`. The identities are stated in `ℂ`. Uniform Cliffords are uniform over Cliffords modulo
global phase (finiteness of the label types as instance arguments). No positivity of `t` is
assumed: it is the milestone Eq. (11). -/
theorem theorem_7 (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ,
      (∀ O : Op (2 * m), O.IsHermitian → ∀ σ : Op (2 * m), WildeQIT.IsDensityOperator σ →
        ((stateShadowNormSq (brickwork m k) O σ : ℝ) : ℂ) =
          (σ * ∑ lam, ∑ lam',
            (coeff O lam * coeff O lam' * (tauCoeff (brickwork m k) lam lam' : ℂ) /
              ((tCoeff (brickwork m k) lam : ℂ) * (tCoeff (brickwork m k) lam' : ℂ))) •
              (pauli lam * pauli lam')).trace) ∧
      (∀ O : Op (2 * m), O.IsHermitian → ∀ σ : Op (2 * m), WildeQIT.IsDensityOperator σ →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ((stateShadowNormSq (brickwork m k) O σ : ℝ) : ℂ) =
            ((lsShadowNormSq (brickwork m k) O 𝓔 : ℝ) : ℂ) + (σ * oTilde (brickwork m k) O).trace) ∧
      (∀ O : Op (2 * m), O.IsHermitian →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ((lsShadowNormSq (brickwork m k) O 𝓔 : ℝ) : ℂ) =
            ∑ lam, coeff O lam ^ 2 / (tCoeff (brickwork m k) lam : ℂ))) ∧
    ((∀ O : Op (2 * m), O.IsHermitian → ∀ σ : Op (2 * m), WildeQIT.IsDensityOperator σ →
        ((stateShadowNormSq (globalClifford (2 * m)) O σ : ℝ) : ℂ) =
          (σ * ∑ lam, ∑ lam',
            (coeff O lam * coeff O lam' * (tauCoeff (globalClifford (2 * m)) lam lam' : ℂ) /
              ((tCoeff (globalClifford (2 * m)) lam : ℂ) * (tCoeff (globalClifford (2 * m)) lam' : ℂ))) •
              (pauli lam * pauli lam')).trace) ∧
      (∀ O : Op (2 * m), O.IsHermitian → ∀ σ : Op (2 * m), WildeQIT.IsDensityOperator σ →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ((stateShadowNormSq (globalClifford (2 * m)) O σ : ℝ) : ℂ) =
            ((lsShadowNormSq (globalClifford (2 * m)) O 𝓔 : ℝ) : ℂ) +
              (σ * oTilde (globalClifford (2 * m)) O).trace) ∧
      (∀ O : Op (2 * m), O.IsHermitian →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ((lsShadowNormSq (globalClifford (2 * m)) O 𝓔 : ℝ) : ℂ) =
            ∑ lam, coeff O lam ^ 2 / (tCoeff (globalClifford (2 * m)) lam : ℂ))) := by sorry

end ShallowShadows.ShadowNorm
