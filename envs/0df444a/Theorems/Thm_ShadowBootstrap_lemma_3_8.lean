-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_3_8
-- name    : ShadowBootstrap.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:28.349963+00:00
-- url     : https://prove2.me/theorems/207db39a-83b6-4e6f-b605-a53168683398
-- title:
--   Lemma 3.8 — $\mathrm{Var}[\mathrm{Tr}(O\hat\rho)] \le C_F\|O\|_F^2$ for the two-layer Clifford ensemble
-- statement:
--   Let $E_{2L}$ be the two-layer Clifford ensemble with block size $k \ge 8$ on $n = km$ qubits ($k$ even), and suppose $k\,2^{k/2} = \Omega(n)$: for a fixed constant $c > 0$, $k\,2^{k/2} \ge c\,n$. Then the shadow channel $\mathcal M$ of $E_{2L}$ is invertible and, for every state $\rho$ and every Hermitian observable $O$, the shadow estimator $\hat\rho = \mathcal M^{-1}(U^\dagger|b\rangle\langle b|U)$ of a record $(U, b)$ drawn from $\rho$ satisfies
--   $$\mathrm{Var}\big[\operatorname{Tr}(O\hat\rho)\big] \le C_F\|O\|_F^2, \qquad C_F = O(1). \tag{8}$$
--   The constant $C_F$ depends only on $c$.
--
--   This is the variance bound on which every later step rests: the residual estimator (Lemma 4.2), the conditional estimator (Lemma 5.9), and through Lemma A.1 the suffix ensembles of Lemma A.2.
--
--   Differences from the source:
--   - reading: k2^{k/2} = Ω(n), C = O(1) → for every c > 0 there is a constant such that the bound holds whenever k·2^{k/2} ≥ c·n; reason: Ω(n) hides a positive constant; the O(1) constant may depend only on it, and is chosen before k, m, the state and the observable
--   - encoding: k an even divisor of n → n = k·m with Even k and m > 0; reason: the same registers
--   - encoding: Cliffords sampled uniformly from Cl(k) → uniform on CliffordLabel k (k-qubit Cliffords modulo global phase), finiteness as an instance argument; reason: all quantities depend on U only through X ↦ UXU†; the published pattern of ShallowShadows.ShadowNorm
--   - reading: Var[Tr(Oρ̂)] for an unnamed state → for every density operator ρ; reason: [COK26, Theorem 1] and Lemma 5.4 apply it to every state
--   - generalization: (conclusion) the variance bound → also: the shadow channel is invertible; reason: ρ̂ = M⁻¹(·) presupposes invertibility (Lemma 3.3: every visibility m_P is positive); the printed bound is the second conjunct
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 3.8, Eq. (8), p.10 (cited from [COK26, Theorem 1])

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_twoLayer

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 3.8, Eq. (8), p.10 (cited from [COK26, Theorem 1]): for the two-layer Clifford ensemble
with block size `k ≥ 8` satisfying `k2^{k/2} = Ω(n)`, every Hermitian observable `O` satisfies
`Var[Tr(Oρ̂)] ≤ C_F ‖O‖_F²` with `C_F = O(1)`.

**Formalization Note** `k2^{k/2} = Ω(n)` is read as `k2^{k/2} ≥ c·n` for a constant `c > 0`; the
constant `C_F` depends on `c` only, and is chosen before `k`, `m`, the state and the observable.
The register has `n = km` qubits (`k` an even divisor of `n`, Definition 3.1). The variance is
under every state `ρ` (the record `(U, b)` is drawn by sampling `U ∼ E2L` and measuring `ρ`);
`snapVar` takes the real part of `Tr(Oρ̂)`, which is real for Hermitian `O`. The statement also
asserts that the shadow channel is invertible, which the definition of `ρ̂ = M⁻¹(U†|b⟩⟨b|U)`
presupposes. -/
theorem lemma_3_8 :
    ∀ c : ℝ, 0 < c → ∃ CF : ℝ, ∀ (k m : ℕ) [Fintype (CliffordLabel k)],
      8 ≤ k → Even k → 0 < m → c * ((k * m : ℕ) : ℝ) ≤ (k : ℝ) * 2 ^ (k / 2) →
        IsUnit (measChannel (twoLayer k m)) ∧
        ∀ ρ : Op (k * m), WildeQIT.IsDensityOperator ρ → ∀ O : Op (k * m), O.IsHermitian →
          snapVar (twoLayer k m) ρ O ≤ CF * frobSq O := by sorry

end ShadowBootstrap
