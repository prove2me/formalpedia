-- Prove2me | Theorems.Thm_QuantumHMMR_eq_17
-- name    : QuantumHMMR.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:48.026274+00:00
-- url     : https://prove2.me/theorems/79017153-5837-41b1-96d8-1169688c13f0
-- title:
--   Eq. (17) — spectrum of $B = M^m - M^{(t)}_{\mu_H}$ and the choice of $A_t$
-- statement:
--   Let $\gamma, a > 0$ be constants for which (13) and (14) hold for all large $n$. For every integer $A \ge 1$, with $m = An^2$, $p = 1/m$, $M = M^{(t)}_{\nu_n}$ and $B = M^m - M^{(t)}_{\mu_H}$, for all sufficiently large $n$:
--
--   1. the Haar eigenvalues of $B$ are zero: $B M^{(t)}_{\mu_H} = 0$;
--   2. $B$ is Hermitian and all its eigenvalues have absolute value at most $\rho = e^{-a/2} < 1$;
--   3. except for at most $D_t$ of them, they have absolute value at most
--   $$
--   \eta_n = \Big(1 - \frac{(1-p)\gamma}{n}\Big)^m \le \exp\Big(-\frac{\gamma m}{2n}\Big). \tag{17}
--   $$
--
--   Moreover the integer $A = A_t \ge 1$ can be chosen so large that, with $d = 2^n$, $d^{2t}\eta_n \le e^{-n}$ for all sufficiently large $n$.
--
--   Differences from the source:
--   - generalization: γ, a are the universal constants of Lemma 4.2 → any γ, a > 0 for which (13) and (14) hold for all large n (IsGapPair G t γ a); reason: the proof uses Lemma 4.2 only through (13) and (14); Lemma 4.2 (milestone lemma_4_2) supplies such a pair, so the statement specializes to the paper's
--   - generalization: B for m = A_t n² → the spectral clauses for every integer A ≥ 1, with n₀ depending on A; reason: they hold for each A ≥ 1 once n is large; A_t is one such A
--   - encoding: eigenvalues of a Hermitian matrix and the min-max count → Mathlib's IsHermitian.eigenvalues (with multiplicity), Hermitian stated as a clause; reason: same eigenvalues
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, Eq. (17), p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_xiLaw
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_Dt
import Definitions.Def_QuantumHMMR_IsGapPair

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45
open scoped Matrix

namespace QuantumHMMR

/-- **Eq. (17)** and the choice of `A_t` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.15). Consider one length-`m`
segment and subtract its Haar moment: `B = M^m - M^{(t)}_{μ_H}`, where `M = M^{(t)}_{ν_n}`,
`m = A n²`, `p = 1/m`. For large `n`: all eigenvalues of `B` have absolute value at most
`ρ = e^{-a/2} < 1`; except for at most `D_t` of them, they have absolute value at most
`η_n = (1 - (1 - p)γ/n)^m ≤ exp(-γm/(2n))` (17); and the Haar eigenvalues of `B` are zero
(`B M^{(t)}_{μ_H} = 0`). Moreover the integer `A = A_t ≥ 1` can be chosen so large that, with
`d = 2ⁿ`, `d^{2t} η_n ≤ e^{-n}` for all large `n`.

Here `γ, a > 0` are constants for which (13) and (14) hold for all large `n` (`IsGapPair G t γ a`).

**Formalization Note** The spectral clauses hold for every integer `A ≥ 1` (with `n₀` depending on
`A`); the last clause chooses `A` depending on `G, t, γ, a`. `B` is Hermitian (a clause); its
eigenvalues, with multiplicity, are Mathlib's `IsHermitian.eigenvalues`. -/
theorem eq_17 [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) :
    (∀ A : ℕ, 1 ≤ A → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let m := A * n ^ 2
      let p : ℝ := (m : ℝ)⁻¹
      let M := balancedUnitaryMoment (stepLaw G n m) t
      let MH := balancedUnitaryMoment (haarLaw n) t
      let B := M ^ m - MH
      let η : ℝ := (1 - (1 - p) * γ / n) ^ m
      B * MH = 0 ∧ B.IsHermitian ∧
      (∀ hB : B.IsHermitian,
        (∀ i, |hB.eigenvalues i| ≤ Real.exp (-(a / 2))) ∧
        (Finset.univ.filter fun i => η < |hB.eigenvalues i|).card ≤ Dt t) ∧
      η ≤ Real.exp (-(γ * m / (2 * n)))) ∧
    Real.exp (-(a / 2)) < 1 ∧
    ∃ A : ℕ, 1 ≤ A ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ)) := by sorry

end QuantumHMMR
