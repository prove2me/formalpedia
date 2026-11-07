-- Prove2me | Theorems.Thm_QuantumHMMR_eq_18
-- name    : QuantumHMMR.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:56.088804+00:00
-- url     : https://prove2.me/theorems/1ae17355-21bb-414b-b042-f751dbc64dc4
-- title:
--   Eq. (18) — the acceptance difference $a_j = \mathrm{Tr}[\Lambda_A^\dagger B^j]$ after $j$ segments
-- statement:
--   Let $\gamma, a > 0$ satisfy (13) and (14) for all large $n$, and let $A \ge 1$ be an integer with $d^{2t}\eta_n \le e^{-n}$ for all large $n$, where $d = 2^n$, $m = An^2$ and $\eta_n = (1 - (1-p)\gamma/n)^m$. With $M = M^{(t)}_{\nu_n}$, $B = M^m - M^{(t)}_{\mu_H}$ and $\rho = e^{-a/2}$, for all sufficiently large $n$ the following holds for every adaptive $t$-query algorithm and measurement $(M_A, I - M_A)$ and every matrix $\Lambda_A$ as in Lemma 4.1, with $a_j = \mathrm{Tr}[\Lambda_A^\dagger B^j]$:
--
--   1. $B^j = M^{mj} - M^{(t)}_{\mu_H}$ for $j \ge 1$;
--   2. $a_j \in [-1, 1]$: it is the difference of the acceptance probabilities under the walk $\nu_n^{*mj}$ and under Haar;
--   3. $a_j = u_j + v_j$ with $u_j = \sum_i b_i\lambda_i^j$ a sum over at most $D_t$ eigenvalues $\lambda_i$ of $B$ larger than $\eta_n$ in absolute value (so $|\lambda_i| \le \rho$), and $|v_j| \le d^{2t}\eta_n^j \le e^{-n}$ for $j \ge 1$;
--   4. for $j \ge D_t$,
--   $$
--   |a_j| \le 2D_t 2^{D_t}\binom{j + D_t - 2}{D_t - 1}\rho^{j - D_t} + e^{-n}. \tag{18}
--   $$
--
--   Differences from the source:
--   - generalization: γ, a are the universal constants of Lemma 4.2 → any γ, a > 0 for which (13) and (14) hold for all large n (IsGapPair G t γ a); reason: the proof uses Lemma 4.2 only through (13) and (14); Lemma 4.2 (milestone lemma_4_2) supplies such a pair, so the statement specializes to the paper's
--   - generalization: m = A_t n² with A_t chosen so that d^{2t} η_n ≤ e^{-n} → any integer A ≥ 1 satisfying d^{2t} η_n ≤ e^{-n} for all large n; reason: this is the only property of A_t used; eq_17 supplies such an A
--   - generalization: Λ_A the matrix from Lemma 4.1 → every Λ with the two properties of Lemma 4.1; reason: the matrix of Lemma 4.1 is one such Λ
--   - reading: a_j ∈ [−1, 1] → a_j equals the real acceptance difference between ν_n^{*mj} and Haar, of absolute value at most 1; reason: this is the reason the page gives for a_j ∈ [−1, 1]
--   - encoding: the at most D_t eigenvalues larger than η_n, with coefficients b_i → k ≤ D_t complex numbers λ_i (with multiplicity), each an eigenvalue of B (Module.End.HasEigenvalue), and coefficients b_i; v_j = a_j − u_j; reason: the same split
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, Eq. (18), p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_walkLaw
import Definitions.Def_QuantumHMMR_AdaptiveAlg
import Definitions.Def_QuantumHMMR_acceptProb
import Definitions.Def_QuantumHMMR_IsAcceptanceMatrix
import Definitions.Def_QuantumHMMR_Dt
import Definitions.Def_QuantumHMMR_IsGapPair

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **Eq. (18)** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.15). Fix any adaptive `t`-query algorithm `A^U` and
measurement `(M_A, I - M_A)`, and let `Λ_A` be the matrix from Lemma 4.1. With `M = M^{(t)}_{ν_n}`,
`m = A n²`, `B = M^m - M^{(t)}_{μ_H}`, `η_n = (1 - (1 - p)γ/n)^m`, `ρ = e^{-a/2}`, `d = 2ⁿ`, for large
`n`:
1. `B^j = M^{mj} - M^{(t)}_{μ_H}` for `j ≥ 1`;
2. the scalar `a_j = Tr[Λ_A† B^j]` lies in `[-1, 1]`: it is the acceptance difference between the
   walk of length `mj` and Haar;
3. `a_j = u_j + v_j`, where `u_j = Σ_i b_i λ_i^j` collects the at most `D_t` eigenvalues `λ_i` of `B`
   larger than `η_n` in absolute value (so `|λ_i| ≤ ρ`), and `|v_j| ≤ d^{2t} η_n^j ≤ e^{-n}` (`j ≥ 1`);
4. for `j ≥ D_t`, `|a_j| ≤ 2 D_t 2^{D_t} C(j + D_t - 2, D_t - 1) ρ^{j - D_t} + e^{-n}` (18).

Hypotheses: `γ, a > 0` satisfy (13), (14) for all large `n` (`IsGapPair`), and the integer `A ≥ 1`
satisfies `d^{2t} η_n ≤ e^{-n}` for all large `n` (the choice of `A_t` made before (18)).

**Formalization Note** "The matrix from Lemma 4.1" is any `Λ` with the two properties of Lemma 4.1.
The eigenvalues `λ_i` are listed with multiplicity as `Fin k → ℂ`, `k ≤ D_t`, each an eigenvalue of
`B` (Mathlib's `Module.End.HasEigenvalue` of `Matrix.toLin' B`); `v_j` is `a_j - u_j`. -/
theorem eq_18 [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA1 : 1 ≤ A)
    (hA : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ alg : AdaptiveAlg n t,
      ∀ Meff : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ, IsEffect Meff →
      ∀ Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
          ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
        IsAcceptanceMatrix alg Meff Λ → traceNorm Λ ≤ ((2 : ℝ) ^ n) ^ (2 * t) →
        let m := A * n ^ 2
        let p : ℝ := (m : ℝ)⁻¹
        let M := balancedUnitaryMoment (stepLaw G n m) t
        let MH := balancedUnitaryMoment (haarLaw n) t
        let B := M ^ m - MH
        let η : ℝ := (1 - (1 - p) * γ / n) ^ m
        let aj : ℕ → ℂ := fun j => (Λᴴ * B ^ j).trace
        (∀ j ≥ 1, B ^ j = M ^ (m * j) - MH) ∧
        (∀ j ≥ 1,
          aj j = (((∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
            ∫ U, acceptProb alg Meff U ∂haarLaw n : ℝ) : ℂ) ∧
          |(∫ U, acceptProb alg Meff U ∂walkLaw G n m (m * j)) -
            ∫ U, acceptProb alg Meff U ∂haarLaw n| ≤ 1) ∧
        (∃ k ≤ Dt t, ∃ b lam : Fin k → ℂ,
          (∀ i, Module.End.HasEigenvalue (Matrix.toLin' B) (lam i) ∧
            η < ‖lam i‖ ∧ ‖lam i‖ ≤ Real.exp (-(a / 2))) ∧
          ∀ j ≥ 1, ‖aj j - ∑ i, b i * lam i ^ j‖ ≤ ((2 : ℝ) ^ n) ^ (2 * t) * η ^ j ∧
            ((2 : ℝ) ^ n) ^ (2 * t) * η ^ j ≤ Real.exp (-(n : ℝ))) ∧
        ∀ j ≥ Dt t, ‖aj j‖ ≤ 2 * Dt t * 2 ^ Dt t * ((j + Dt t - 2).choose (Dt t - 1) : ℝ) *
          Real.exp (-(a / 2)) ^ (j - Dt t) + Real.exp (-(n : ℝ)) := by sorry

end QuantumHMMR
