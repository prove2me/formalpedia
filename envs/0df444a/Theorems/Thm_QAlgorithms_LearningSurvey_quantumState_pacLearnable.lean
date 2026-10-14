-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_quantumState_pacLearnable
-- name    : QAlgorithms.LearningSurvey.quantumState_pacLearnable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:58.54724+00:00
-- url     : https://prove2.me/theorems/909836c3-685b-4e93-8b4b-1b6f23a4c7a7
-- title:
--   Quantum states are PAC-learnable from n·poly(1/ε, 1/γ, log(1/δ)) measurement results
-- statement:
--   This is Aaronson's theorem on "pretty good tomography": an $n$-qubit state can be PAC-learned from linearly many (in $n$) measurement results.
--
--   An $n$-qubit state is a density matrix $\rho\in\mathbb C^{2^n\times 2^n}$ (positive semidefinite, trace $1$). A two-outcome measurement is an effect $E$, i.e. $0\preceq E\preceq \mathrm{Id}$; its first outcome has probability $\mathrm{Tr}(E\rho)$. Let $D$ be a probability distribution (Borel) on the set of effects.
--
--   There is a polynomial $p$ in three variables with nonnegative coefficients such that for every $n$ and all $\varepsilon,\gamma>0$, $\delta\in(0,1)$ there are a number
--
--   $$
--   T\ \le\ n\cdot p\big(1/\varepsilon,\ 1/\gamma,\ \log(1/\delta)\big)
--   $$
--
--   and a (measurable) learner $L$, mapping $T$ measurement results to an $n$-qubit density matrix, with the following property: for every $n$-qubit state $\rho$ and every distribution $D$, if $E_1,\dots,E_T$ are drawn i.i.d. from $D$ and, independently given the $E_i$, each $b_i$ is a bit with $\Pr[b_i=1]=\mathrm{Tr}(E_i\rho)$, then with probability at least $1-\delta$ the output $\sigma=L((E_1,b_1),\dots,(E_T,b_T))$ satisfies
--
--   $$
--   \Pr_{E\sim D}\big[\,|\mathrm{Tr}(E\sigma)-\mathrm{Tr}(E\rho)|>\gamma\,\big]\ \le\ \varepsilon .
--   $$
--
--   The learner knows neither $\rho$ nor $D$. Only the number of measurement results is bounded, not the running time.
--
--   **Formalization Note** "$T=n\cdot\mathrm{poly}$" is read as an upper bound on $T$ (a learner may ignore extra results). The condition $\delta<1$ is added: for $\delta\ge 1$ the claim is empty and $\log(1/\delta)\le 0$. The learner is deterministic and measurable; the probability of success is written out as an integral over $D^{T}$ of the probabilities of the bit strings.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 15, Theorem 4.16. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

open MeasureTheory QAlgorithms.Learning




open Classical in
/-- survey p.15, Theorem 4.16 ([Aar07]): PAC learnability of quantum states. There is a
polynomial `p` such that for every number of qubits `n` and all `δ, ε, γ > 0` there is a learner
using `T ≤ n · p(1/ε, 1/γ, log(1/δ))` measurement results with the following property: for every
`n`-qubit state `ρ` and every distribution `D` on the two-outcome measurements (effects `E`,
`0 ≤ E ≤ Id`), given `(E₁, b₁), …, (E_T, b_T)` with the `Eᵢ` i.i.d. from `D` and, independently
given the `Eᵢ`, `Pr[bᵢ = 1] = Tr(Eᵢ ρ)`, with probability `≥ 1 − δ` the learner outputs (the
classical description of) a state `σ` with `Pr_{E∼D}[|Tr(Eσ) − Tr(Eρ)| > γ] ≤ ε`.

The learner is a measurable deterministic map from the `T` results to density matrices; it is
chosen before `ρ` and `D`. `δ < 1` is added (for `δ ≥ 1` the claim is empty, and `log(1/δ) ≤ 0`
would make the bound on `T` meaningless). The joint law of the results is written out: the
`Eᵢ` from the product measure `D^T`, then the bits with probability `∏ᵢ Pr[bᵢ | Eᵢ]`. -/
theorem quantumState_pacLearnable :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ s, 0 ≤ p.coeff s) ∧
      ∀ (n : ℕ) (ε γ δ : ℝ), 0 < ε → 0 < γ → 0 < δ → δ < 1 →
      ∃ T : ℕ, (T : ℝ) ≤ (n : ℝ) * MvPolynomial.eval ![1 / ε, 1 / γ, Real.log (1 / δ)] p ∧
      ∃ L : (Fin T → EffectSet n × Bool) → Matrix (Qubits n) (Qubits n) ℂ,
        Measurable (fun s (i j : Qubits n) => L s i j) ∧ (∀ s, IsDensityMatrix (L s)) ∧
        ∀ ρ : Matrix (Qubits n) (Qubits n) ℂ, IsDensityMatrix ρ →
        ∀ (D : Measure (EffectSet n)) [IsProbabilityMeasure D],
          ∫⁻ Es, ∑ bs : Fin T → Bool,
              ENNReal.ofReal (∏ i, if bs i then effectProb (Es i).1 ρ
                else 1 - effectProb (Es i).1 ρ) *
              (if D {E | γ < |effectProb E.1 (L fun i => (Es i, bs i)) - effectProb E.1 ρ|} ≤
                  ENNReal.ofReal ε then 1 else 0)
            ∂(Measure.pi fun _ : Fin T => D) ≥ ENNReal.ofReal (1 - δ) := by sorry

end QAlgorithms.LearningSurvey
