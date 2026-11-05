-- Prove2me | Theorems.Thm_ShallowShadows_ShadowNorm_eq_11_inverse
-- name    : ShallowShadows.ShadowNorm.eq_11_inverse
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:09.444777+00:00
-- url     : https://prove2.me/theorems/4da5e79d-d262-4a02-abce-700d985a13f3
-- title:
--   Eq. (11): $t_{\lambda,d}>0$, $\mathcal M_d$ is invertible and $\mathcal M_d^{-1}(P^\lambda)=P^\lambda/t_{\lambda,d}$
-- statement:
--   Let $n = 2m$ and $d\in\{\infty,0,1,2,\dots\}$. For every $\lambda\in\{0,1\}^{2n}$ the probability $t_{\lambda,d}$ is nonzero, the measurement channel $\mathcal M_d$ is invertible, and its inverse is
--
--   $$
--   \mathcal M_d^{-1}(P^\lambda) = \frac{1}{t_{\lambda,d}}\,P^\lambda.
--   $$
--
--   Invertibility of the measurement channel is what makes the classical shadow $\mathcal M_d^{-1}(U^\dagger|b\rangle\langle b|U)$ an unbiased estimator of the state.
--
--   Differences from the source:
--   - encoding: uniformly random single-qubit, two-qubit and n-qubit Clifford gates → uniform distribution on CliffordLabel k (k-qubit Cliffords modulo global phase), with [Fintype (CliffordLabel k)] as instance arguments; reason: every quantity depends on U only through X ↦ UXU†, the quotient is finite so the instances exist, and Fintype is a subsingleton so the uniform law does not depend on the instance
--   - encoding: n (even) qubits → n = 2m, m : ℕ; reason: same instances; m = 0 is the degenerate 0-qubit case
--   - encoding: every depth d ∈ {∞, 0, 1, …} → a conjunction: ∀ k : ℕ for brickwork m k, and globalClifford (2m) for d = ∞; reason: the two cases have different label types; both are stated in full
--   - reading: nearest-neighbour circular brickwork pattern, first and last qubit neighbours (p. 4, Fig. 1) → 0-based qubits; the paper's odd layers act on (2p, 2p+1), even layers on (2p+1, (2p+2) mod 2m); U = L_d ⋯ L_1 L_0; reason: fixed by Fig. 1's caption (layer 2 contains the pair (8, 1)) and by 'first applying … the 0th layer then for each layer i ∈ [d]'
--   - encoding: M^{-1}, the inverse of the measurement channel M_d → ClassicalShadow.Linear.measChannelInv = Ring.inverse (measChannel E); reason: Ring.inverse is the inverse whenever M_d is a unit, which holds for every U_d (Eq. (11), milestone)
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §V, Eq. (11), p. 5

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_brickwork
import Definitions.Def_ShallowShadows_ShadowNorm_globalClifford
import Definitions.Def_ShallowShadows_ShadowNorm_tCoeff

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §V, Eq. (11), p. 5:
"for any `λ ∈ {0,1}^{2n}`, the probability `t_{λ,d}` is non-zero ensuring non-singularity and
that the inverse is given by `M_d^{-1}(P^λ) = (1/t_{λ,d}) P^λ`."

Stated for every `m` (`n = 2m`) and every depth (`𝒰_k`, `k ∈ ℕ`, and `𝒰_∞`): every `t_{λ,d}` is
positive, the measurement channel `M_d` of Eq. (2) is invertible, and its inverse
(`ClassicalShadow.Linear.measChannelInv = Ring.inverse M_d`) maps `P^λ` to `t_{λ,d}^{-1} P^λ`. -/
theorem eq_11_inverse (m : ℕ) [Fintype (CliffordLabel 1)] [Fintype (CliffordLabel 2)]
    [Fintype (CliffordLabel (2 * m))] :
    (∀ k : ℕ, (∀ lam : Bits (2 * m) × Bits (2 * m), 0 < tCoeff (brickwork m k) lam) ∧
        IsUnit (measChannel (brickwork m k)) ∧
        ∀ lam : Bits (2 * m) × Bits (2 * m),
          measChannelInv (brickwork m k) (pauli lam) = ((tCoeff (brickwork m k) lam : ℂ))⁻¹ • pauli lam) ∧
      ((∀ lam : Bits (2 * m) × Bits (2 * m), 0 < tCoeff (globalClifford (2 * m)) lam) ∧
        IsUnit (measChannel (globalClifford (2 * m))) ∧
        ∀ lam : Bits (2 * m) × Bits (2 * m),
          measChannelInv (globalClifford (2 * m)) (pauli lam) =
            ((tCoeff (globalClifford (2 * m)) lam : ℂ))⁻¹ • pauli lam) := by sorry

end ShallowShadows.ShadowNorm
