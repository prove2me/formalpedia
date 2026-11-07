-- Prove2me | Theorems.Thm_QuantumHMMR_eigenvalue_count
-- name    : QuantumHMMR.eigenvalue_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:37.61608+00:00
-- url     : https://prove2.me/theorems/e353a34b-4340-474b-9cc7-c916228b32d3
-- title:
--   Proof of Theorem 1.3, p.15 — at most $D_t$ eigenvalues of $M$ exceed $1 - (1-p)\gamma/n$
-- statement:
--   With $\gamma, a$, $A$, $m = An^2$, $p = 1/m$ and $M = M^{(t)}_{\nu_n}$ as in Eq. (16), and $\theta = 1 - (1-p)\gamma/n$, for all sufficiently large $n$:
--
--   1. on $\ker M^{(t)}_{\mathcal C_n}$ the Rayleigh quotient of $M$ is at most $\theta$;
--   2. $\ker M^{(t)}_{\mathcal C_n}$ has codimension at most $D_t$;
--   3. $M$ is Hermitian and, by the min-max principle, at most $D_t$ of its eigenvalues exceed $\theta$;
--   4. $M \succeq -\theta I$, so every negative eigenvalue of $M$ has absolute value at most $\theta$.
--
--   Together with (16) this pins down the spectrum of $M$ outside the Haar-invariant subspace.
--
--   Differences from the source:
--   - generalization: γ, a are the universal constants of Lemma 4.2 → any γ, a > 0 for which (13) and (14) hold for all large n (IsGapPair G t γ a); reason: the proof uses Lemma 4.2 only through (13) and (14); Lemma 4.2 (milestone lemma_4_2) supplies such a pair, so the statement specializes to the paper's
--   - generalization: m = A_t n² for the A_t chosen before (18) → every integer A ≥ 1, with n₀ depending on A; reason: the step holds for each A ≥ 1 once n is large; A_t is one such A
--   - encoding: quadratic forms ⟨v, Xv⟩ and norms ‖v‖² of vectors in (ℂ^d)^{⊗2t} → Re(star v ⬝ᵥ X v) and Re(star v ⬝ᵥ v) on functions of the index set; reason: the operators are Hermitian, so the forms are real; the explicit dot product avoids the sup norm of the function type
--   - encoding: eigenvalues of a Hermitian matrix and the min-max count → Mathlib's IsHermitian.eigenvalues (with multiplicity), Hermitian stated as a clause; reason: same eigenvalues
--   - encoding: codimension of ker M^{(t)}_{C_n} → rank of M^{(t)}_{C_n}; reason: equal by rank–nullity
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, p.15

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

/-- **Low-eigenvalue count** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.15). With `p = 1/m`, `m = A n²`,
`M = M^{(t)}_{ν_n}` and `θ = 1 - (1 - p)γ/n`: on `ker M^{(t)}_{C_n}` the Rayleigh quotient of `M` is at
most `θ`; `ker M^{(t)}_{C_n}` has codimension at most `D_t`; by the min-max principle at most `D_t`
eigenvalues of `M` exceed `θ`; and `M ⪰ -θ I`, so every negative eigenvalue has absolute value at
most `θ`. This holds for all sufficiently large `n`, for constants `γ, a > 0` satisfying (13) and
(14) for all large `n`.

**Formalization Note** `M` is Hermitian (stated as a clause) and its eigenvalues, with multiplicity,
are Mathlib's `IsHermitian.eigenvalues`. The codimension of the kernel is the rank of
`M^{(t)}_{C_n}`. Quadratic forms as in `eq_16`. -/
theorem eigenvalue_count [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA : 1 ≤ A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p : ℝ := ((A * n ^ 2 : ℕ) : ℝ)⁻¹
      let M := balancedUnitaryMoment (stepLaw G n (A * n ^ 2)) t
      let MC := balancedUnitaryMoment (cliffordLaw n) t
      let θ : ℝ := 1 - (1 - p) * γ / n
      (∀ v, MC *ᵥ v = 0 → (star v ⬝ᵥ (M *ᵥ v)).re ≤ θ * (star v ⬝ᵥ v).re) ∧
      MC.rank ≤ Dt t ∧
      M.IsHermitian ∧
      (∀ hM : M.IsHermitian,
        (Finset.univ.filter fun i => θ < hM.eigenvalues i).card ≤ Dt t ∧
        ∀ i, hM.eigenvalues i < 0 → |hM.eigenvalues i| ≤ θ) ∧
      (M + (θ : ℂ) • (1 : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
        ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ)).PosSemidef := by sorry

end QuantumHMMR
