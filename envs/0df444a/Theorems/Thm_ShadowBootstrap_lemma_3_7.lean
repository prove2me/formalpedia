-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_3_7
-- name    : ShadowBootstrap.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:50.470184+00:00
-- url     : https://prove2.me/theorems/3f4f459d-b81a-4d73-92c0-515752a66a01
-- title:
--   Lemma 3.7 — $\|\mathbb E\hat\rho^2\|_{op} = O(d)$ for the two-layer Clifford ensemble
-- statement:
--   Let $E_{2L}$ be the two-layer Clifford ensemble with block size $k \ge 2$ on $n = km$ qubits ($k$ even), and suppose $k\,2^{k/2} \ge c\,n$ for a fixed constant $c > 0$. Then the shadow channel is invertible and, for every state $\rho$ from which the outcome $b$ is drawn,
--   $$\big\|\mathbb E\,\hat\rho^2\big\|_{op} = \big\|\mathbb E\,\mathcal M^{-1}(U^\dagger|b\rangle\langle b|U)^2\big\|_{op} = O(d), \qquad d = 2^n, \tag{7}$$
--   with the $O(\cdot)$ constant depending only on $c$.
--
--   It bounds the finite-shot fluctuation of the residual estimator in the proof of Lemma 4.2.
--
--   Differences from the source:
--   - reading: k2^{k/2} = Ω(n), C = O(1) → for every c > 0 there is a constant such that the bound holds whenever k·2^{k/2} ≥ c·n; reason: Ω(n) hides a positive constant; the O(1) constant may depend only on it, and is chosen before k, m, the state and the observable
--   - encoding: k an even divisor of n → n = k·m with Even k and m > 0; reason: the same registers
--   - encoding: Cliffords sampled uniformly from Cl(k) → uniform on CliffordLabel k (k-qubit Cliffords modulo global phase), finiteness as an instance argument; reason: all quantities depend on U only through X ↦ UXU†; the published pattern of ShallowShadows.ShadowNorm
--   - reading: b drawn from an unnamed state → for every density operator ρ measured in the basis U; reason: Lemma 4.2 applies it to the unknown state
--   - generalization: (conclusion) the norm bound → also: the shadow channel is invertible; reason: ρ̂ presupposes invertibility; the printed bound is the second conjunct
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 3.7, Eq. (7), p.10 (cited from [CK25a, Appendix D])

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_twoLayer
import Definitions.Def_ShadowBootstrap_shadowSecondMoment

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 3.7, Eq. (7), p.10 (cited from [CK25a, Appendix D]): for the two-layer Clifford ensemble with
block size `k ≥ 2` satisfying `k2^{k/2} = Ω(n)`,
`‖E ρ̂²‖_op = ‖E M⁻¹(U†|b⟩⟨b|U)²‖_op = O(d)`, `d = 2ⁿ`.

**Formalization Note** `k2^{k/2} = Ω(n)` is read as `k2^{k/2} ≥ c·n` for a constant `c > 0`; the
`O(d)` constant depends on `c` only. The register has `n = km` qubits (`k` an even divisor of `n`).
The outcome `b` is drawn from the state `ρ` measured in the basis `U`, for every state `ρ` (the
lemma names no state; Lemma 4.2 uses it for the unknown state). The statement also asserts that
the shadow channel is invertible, which `ρ̂ = M⁻¹(U†|b⟩⟨b|U)` presupposes. -/
theorem lemma_3_7 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ (k m : ℕ) [Fintype (CliffordLabel k)],
      2 ≤ k → Even k → 0 < m → c * ((k * m : ℕ) : ℝ) ≤ (k : ℝ) * 2 ^ (k / 2) →
        IsUnit (measChannel (twoLayer k m)) ∧
        ∀ ρ : Op (k * m), WildeQIT.IsDensityOperator ρ →
          opNorm (shadowSecondMoment (twoLayer k m) ρ) ≤ C * 2 ^ (k * m) := by sorry

end ShadowBootstrap
