-- Prove2me | Theorems.Thm_QuantumHMMR_eq_16
-- name    : QuantumHMMR.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:31.551763+00:00
-- url     : https://prove2.me/theorems/417a27f6-4fd5-4c07-b372-72957209358b
-- title:
--   Eq. (16) — gap of order $1/m$ of $M^{(t)}_{\nu_n}$ outside the Haar-invariant subspace
-- statement:
--   Let $\gamma, a > 0$ be constants for which (13) and (14) hold for all large $n$, let $A \ge 1$ be an integer, and set $m = An^2$, $p = 1/m$ and
--   $$
--   M = M^{(t)}_{\nu_n} = (1-p)M^{(t)}_{\chi_n} + pM^{(t)}_{\xi_n}.
--   $$
--   For all sufficiently large $n$: $M$ fixes the Haar-invariant subspace, $M M^{(t)}_{\mu_H} = M^{(t)}_{\mu_H} = M^{(t)}_{\mu_H} M$; $I - M^{(t)}_{\xi_n}$ is positive semidefinite with norm at most two; and for every $v$ orthogonal to the image of $M^{(t)}_{\mu_H}$, with $x = M^{(t)}_{\mathcal C_n}v$ and $y = v - x$,
--   $$
--   \langle v, (I - M^{(t)}_{\xi_n})v\rangle \ge \tfrac12\langle x, (I - M^{(t)}_{\xi_n})x\rangle - \langle y, (I - M^{(t)}_{\xi_n})y\rangle \ge \tfrac a2\|x\|^2 - 2\|y\|^2,
--   $$
--   $$
--   \langle v, (I - M)v\rangle \ge \frac{ap}{2}\|x\|^2 + \Big(\frac{(1-p)\gamma}{n} - 2p\Big)\|y\|^2 \ge \frac{ap}{2}\|v\|^2. \tag{16}
--   $$
--
--   This is the gap of the one-step moment operator outside the Haar-invariant subspace, the first step of the proof of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: γ, a are the universal constants of Lemma 4.2 → any γ, a > 0 for which (13) and (14) hold for all large n (IsGapPair G t γ a); reason: the proof uses Lemma 4.2 only through (13) and (14); Lemma 4.2 (milestone lemma_4_2) supplies such a pair, so the statement specializes to the paper's
--   - generalization: m = A_t n² for the A_t chosen before (18) → every integer A ≥ 1, with n₀ depending on A; reason: the step holds for each A ≥ 1 once n is large; A_t is one such A
--   - encoding: quadratic forms ⟨v, Xv⟩ and norms ‖v‖² of vectors in (ℂ^d)^{⊗2t} → Re(star v ⬝ᵥ X v) and Re(star v ⬝ᵥ v) on functions of the index set; reason: the operators are Hermitian, so the forms are real; the explicit dot product avoids the sup norm of the function type
--   - encoding: v orthogonal to the image of M^{(t)}_{μ_H} → ⟨v, M^{(t)}_{μ_H} w⟩ = 0 for every w; reason: the definition of orthogonality to the image
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, Eq. (16), pp.14–15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_xiLaw
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_Dt
import Definitions.Def_QuantumHMMR_IsGapPair

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45
open scoped Matrix ComplexOrder

namespace QuantumHMMR

/-- **Eq. (16)** and the invariance of the Haar subspace (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, pp.14–15).
Set `p = 1/m`, `m = A n²`, and `M = M^{(t)}_{ν_n} = (1 - p) M^{(t)}_{χ_n} + p M^{(t)}_{ξ_n}`. The
moment operators fix the Haar-invariant subspace: `M M^{(t)}_{μ_H} = M^{(t)}_{μ_H} = M^{(t)}_{μ_H} M`.
For `v` orthogonal to the image of `M^{(t)}_{μ_H}`, write `x = M^{(t)}_{C_n} v`, `y = v - x`. Then
`I - M^{(t)}_{ξ_n}` is positive semidefinite with norm at most two,
`⟨v, (I - M_ξ) v⟩ ≥ ½⟨x, (I - M_ξ) x⟩ - ⟨y, (I - M_ξ) y⟩ ≥ (a/2)‖x‖² - 2‖y‖²`, and
`⟨v, (I - M) v⟩ ≥ (ap/2)‖x‖² + ((1 - p)γ/n - 2p)‖y‖² ≥ (ap/2)‖v‖²` (16), for sufficiently large `n`.

Here `γ, a > 0` are constants for which (13) and (14) of Lemma 4.2 hold for all large `n`
(`IsGapPair G t γ a`).

**Formalization Note** Vectors are functions on the index set of `U^{⊗t} ⊗ Ū^{⊗t}`; `⟨u, w⟩` is
`star u ⬝ᵥ w` and `‖u‖² = Re ⟨u, u⟩` (never the sup norm of the function type). Each quadratic form
is compared through its real part (the operators are Hermitian, so the forms are real).
Orthogonality to the image of `M^{(t)}_{μ_H}` is `⟨v, M^{(t)}_{μ_H} w⟩ = 0` for all `w`. `n₀`
depends on `G, t, γ, a, A`. -/
theorem eq_16 [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA : 1 ≤ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p : ℝ := ((A * n ^ 2 : ℕ) : ℝ)⁻¹
      let M := balancedUnitaryMoment (stepLaw G n (A * n ^ 2)) t
      let MC := balancedUnitaryMoment (cliffordLaw n) t
      let MH := balancedUnitaryMoment (haarLaw n) t
      let Mξ := balancedUnitaryMoment (xiLaw n) t
      M * MH = MH ∧ MH * M = MH ∧ (1 - Mξ).PosSemidef ∧ specNorm (1 - Mξ) ≤ 2 ∧
      ∀ v, (∀ w, star v ⬝ᵥ (MH *ᵥ w) = 0) →
        let x := MC *ᵥ v
        let y := v - x
        (1 / 2) * (star x ⬝ᵥ ((1 - Mξ) *ᵥ x)).re - (star y ⬝ᵥ ((1 - Mξ) *ᵥ y)).re ≤
          (star v ⬝ᵥ ((1 - Mξ) *ᵥ v)).re ∧
        (a / 2) * (star x ⬝ᵥ x).re - 2 * (star y ⬝ᵥ y).re ≤
          (1 / 2) * (star x ⬝ᵥ ((1 - Mξ) *ᵥ x)).re - (star y ⬝ᵥ ((1 - Mξ) *ᵥ y)).re ∧
        (a * p / 2) * (star x ⬝ᵥ x).re + ((1 - p) * γ / n - 2 * p) * (star y ⬝ᵥ y).re ≤
          (star v ⬝ᵥ ((1 - M) *ᵥ v)).re ∧
        (a * p / 2) * (star v ⬝ᵥ v).re ≤
          (a * p / 2) * (star x ⬝ᵥ x).re + ((1 - p) * γ / n - 2 * p) * (star y ⬝ᵥ y).re := by sorry

end QuantumHMMR
