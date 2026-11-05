-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_eq_F8
-- name    : ShallowShadows.ShadowNorm.eq_F8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:41.915357+00:00
-- url     : https://prove2.me/theorems/103885ff-46a1-46b9-b459-4ddb8e5ac907
-- title:
--   Eq. (F8): $\mathbb E_{\sigma\sim\mathcal E}[\operatorname{tr}(\sigma\tilde O)] = 2^{-n}\operatorname{tr}(\tilde O) = 0$ for a state one-design
-- statement:
--   Let $n = 2m$, $d\in\{\infty,0,1,2,\dots\}$, $O$ an observable and $\tilde O$ the operator of Eq. (21) for the ensemble $\mathcal U_d$. For every state one-design $\mathcal E$ ($\mathbb E_{\sigma\sim\mathcal E}[\sigma] = \mathbb I/2^n$),
--
--   $$
--   \mathbb E_{\sigma\sim\mathcal E}\big[\operatorname{tr}(\sigma\tilde O)\big] = \frac{1}{2^n}\operatorname{tr}(\tilde O) = 0.
--   $$
--
--   It identifies the state independent part of the shadow norm in Theorem 7 with the locally scrambled shadow norm.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
--   - reading: any observable O → any Hermitian matrix O (O.IsHermitian); reason: an observable is a Hermitian operator, as in the HKP setting the paper builds on
--   - generalization: any ensemble of states E with E_{σ∼E}[σ] = I/2^n → any probability measure 𝓔 on density operators with entrywise mean ∫ σ_ab d𝓔 = 2^{-n} δ_ab (IsStateOneDesign); reason: every finite ensemble of states is such a measure, so the statement specializes to the source's ensembles; the entrywise mean is the matrix identity E[σ] = I/2^n
--   - encoding: real identities → identities in ℂ, real quantities cast to ℂ; β_λ = 2^{-n} tr(P^λ O) complex-valued; reason: β is real for Hermitian O; working in ℂ drops no imaginary part
--   - encoding: O = Σ_λ β_λ P^λ → β_λ := 2^{-n} tr(P^λ O) (coeff); reason: tr(P^λ P^λ') = 2^n δ_λλ' makes the Pauli decomposition of every O unique, with these coefficients
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Appendix F, Eq. (F8), p. 19

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_oTilde
import Definitions.Def_ShallowShadows_ShadowNorm_IsStateOneDesign

open ClassicalShadow.Linear MeasureTheory

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Appendix F, Eq. (F8),
p. 19: for a state one-design `ℰ`, `E_{σ∼ℰ}[tr(σ Õ)] = (1/2ⁿ) tr(Õ) = 0`, with `Õ` of Eq. (21).

Stated for every `m` (`n = 2m`), every depth (`𝒰_k`, `k ∈ ℕ`, and `𝒰_∞`), every observable
(Hermitian matrix) `O` and every state one-design `ℰ` (a probability measure on density operators
with mean `𝕀/2ⁿ`). -/
theorem eq_F8 (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ, ∀ O : Op (2 * m), O.IsHermitian →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ∫ σ, (σ.1 * oTilde (brickwork m k) O).trace ∂𝓔 =
              ((2 : ℂ) ^ (2 * m))⁻¹ * (oTilde (brickwork m k) O).trace ∧
            (oTilde (brickwork m k) O).trace = 0) ∧
      (∀ O : Op (2 * m), O.IsHermitian →
        ∀ 𝓔 : Measure {σ : Op (2 * m) // WildeQIT.IsDensityOperator σ}, IsStateOneDesign 𝓔 →
          ∫ σ, (σ.1 * oTilde (globalClifford (2 * m)) O).trace ∂𝓔 =
              ((2 : ℂ) ^ (2 * m))⁻¹ * (oTilde (globalClifford (2 * m)) O).trace ∧
            (oTilde (globalClifford (2 * m)) O).trace = 0) := by sorry

end ShallowShadows.ShadowNorm
