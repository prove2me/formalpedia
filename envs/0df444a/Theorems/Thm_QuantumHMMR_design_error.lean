-- Prove2me | Theorems.Thm_QuantumHMMR_design_error
-- name    : QuantumHMMR.design_error
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:59.804258+00:00
-- url     : https://prove2.me/theorems/43b5210e-c5a0-4791-8ce2-82b6013c1504
-- title:
--   Proof of Theorem 1.3, p.15 — the design error $\delta_t(\nu_n^{*T}, \mu_H) \le e^{-2\kappa_t \log^2 n}$
-- statement:
--   Let $\gamma, a$ and $A$ be as in Eq. (18). Choose $j = 3\lceil \log^2 n\rceil$, so that $T = mj = 3m\lceil\log^2 n\rceil$. Since $D_t$ is fixed and $\rho < 1$, the polynomial factor in (18) is dominated by the exponential decay: there is $\kappa_t > 0$ such that for all sufficiently large $n$, for every algorithm, measurement and matrix $\Lambda_A$ as in Lemma 4.1,
--   $$
--   |a_{T/m}| = \big|\mathrm{Tr}[\Lambda_A^\dagger B^{T/m}]\big| \le e^{-2\kappa_t \log^2 n},
--   $$
--   and therefore
--   $$
--   \delta_t(\nu_n^{*T}, \mu_H) \le e^{-2\kappa_t \log^2 n}.
--   $$
--
--   This is the design half of Theorem 1.3, Eq. (10).
--
--   Differences from the source:
--   - generalization: γ, a are the universal constants of Lemma 4.2 → any γ, a > 0 for which (13) and (14) hold for all large n (IsGapPair G t γ a); reason: the proof uses Lemma 4.2 only through (13) and (14); Lemma 4.2 (milestone lemma_4_2) supplies such a pair, so the statement specializes to the paper's
--   - generalization: m = A_t n² with A_t chosen so that d^{2t} η_n ≤ e^{-n} → any integer A ≥ 1 satisfying d^{2t} η_n ≤ e^{-n} for all large n; reason: this is the only property of A_t used; eq_17 supplies such an A
--   - generalization: Λ_A the matrix from Lemma 4.1 → every Λ with the two properties of Lemma 4.1; reason: the matrix of Lemma 4.1 is one such Λ
--   - reading: log² n, base not printed → (log_β n)² for an arbitrary base β > 1; reason: covers every reading of the base
--   - encoding: δ_t(ν, μ_H) ∈ [0, 1] → the ℝ≥0∞-valued advantage; reason: same value; no junk supremum
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_AdaptiveAlg
import Definitions.Def_QuantumHMMR_IsAcceptanceMatrix
import Definitions.Def_QuantumHMMR_advantage
import Definitions.Def_QuantumHMMR_logSq
import Definitions.Def_QuantumHMMR_IsGapPair

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **The design error** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.15). Choose `j = 3⌈log² n⌉`, so that
`T = mj = 3m⌈log² n⌉`. Since `D_t` is fixed and `ρ < 1`, `|a_{T/m}| ≤ e^{-2κ_t log² n}` for a constant
`κ_t > 0` and all large `n`, for every algorithm and measurement (with `Λ_A` from Lemma 4.1 and
`B = M^m - M^{(t)}_{μ_H}`); hence `δ_t(ν_n^{*T}, μ_H) ≤ e^{-2κ_t log² n}`.

Hypotheses as in `eq_18`: `γ, a > 0` satisfy (13), (14) for large `n`, and `A ≥ 1` satisfies
`d^{2t} η_n ≤ e^{-n}` for large `n`.

**Formalization Note** `log² n = (log_β n)²` for an arbitrary base `β > 1`; `κ` may depend on `β`.
`δ_t` is the `ℝ≥0∞`-valued `advantage`. -/
theorem design_error [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA1 : 1 ≤ A)
    (hA : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ)))
    (β : ℝ) (hβ : 1 < β) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let m := A * n ^ 2
      let M := balancedUnitaryMoment (stepLaw G n m) t
      let MH := balancedUnitaryMoment (haarLaw n) t
      let B := M ^ m - MH
      (∀ alg : AdaptiveAlg n t,
        ∀ Meff : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ, IsEffect Meff →
        ∀ Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
            ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
          IsAcceptanceMatrix alg Meff Λ → traceNorm Λ ≤ ((2 : ℝ) ^ n) ^ (2 * t) →
          ‖(Λᴴ * B ^ (3 * ⌈logSq β n⌉₊)).trace‖ ≤ Real.exp (-(2 * κ * logSq β n))) ∧
      advantage t (walkLaw G n m (3 * m * ⌈logSq β n⌉₊)) (haarLaw n) ≤
        ENNReal.ofReal (Real.exp (-(2 * κ * logSq β n))) := by sorry

end QuantumHMMR
