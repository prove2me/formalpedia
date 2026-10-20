-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_worst_case_expurgation
-- name    : QAlgorithms.Papers.Independent.Information100.P56.worst_case_expurgation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:20:20.33375+00:00
-- url     : https://prove2.me/theorems/2fbaa295-6c17-42a8-a59d-850de024886a
-- title:
--   Remark V.4: expurgation for every message distribution
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. For a uniform message, let $e_m\in[0,1]$ be its conditional decoding error and $\omega_m$ its Eve state. Set $\epsilon$ to the average error, $\bar\omega$ to the old uniform Eve marginal, and $\delta=\mathbb E_m\|\omega_m-\bar\omega\|_1$. Retain messages with $e_m\le\sqrt\epsilon$ and $\|\omega_m-\bar\omega\|_1\le\sqrt\delta$. The retained set $A$ satisfies
--
--   $$|A|\ge(1-\sqrt\epsilon-\sqrt\delta)|M|.$$
--
--   It is nonempty whenever that lower fraction is positive. Every prior $q$ supported on $A$ has average error at most $\sqrt\epsilon$ and leakage, computed against its own new Eve marginal, at most $2\sqrt\delta$. Along reliable secure code families, the normalized logarithmic message-count loss tends to zero, including when the output dimension varies with blocklength. This converts the uniform-message criterion to every retained-message prior.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 11, Remark V.4: expurgation for every message distribution

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Remark V.4, p.11: expurgation for every message prior, old/new Eve marginals
kept distinct; zero error/leakage use square roots directly, with no divisions by them.
The final clause states the unchanged asymptotic log-message rate. -/
theorem worst_case_expurgation
    {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    {M E : Type*} [Fintype M] [Nonempty M] [Fintype E] [DecidableEq E] [Nonempty E]
    (err : M → ℝ) (W : M → Matrix E E ℂ)
    (herr : ∀ m, err m ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ m, QAlgorithms.IsDensityMatrix (W m)) :
    let eps := ∑ m, uniform m * err m
    let leakage := ensembleLeakage uniform W
    let good := retained err W
    (1 - Real.sqrt eps - Real.sqrt leakage) * Fintype.card M ≤ (good.card : ℝ) ∧
    (0 < 1 - Real.sqrt eps - Real.sqrt leakage → good.Nonempty) ∧
    (∀ m ∈ good, err m ≤ Real.sqrt eps ∧
      QAlgorithms.traceNorm (W m - average W uniform) ≤ Real.sqrt leakage) ∧
    (∀ P : M → ℝ, IsLaw P → (∀ m, m ∉ good → P m = 0) →
      (∑ m, P m * err m) ≤ Real.sqrt eps ∧ ensembleLeakage P W ≤ 2 * Real.sqrt leakage) ∧
    (∀ (counts : ℕ → ℕ) (positive : ∀ n, 0 < counts n)
      (errors : (n : ℕ) → Fin (counts n) → ℝ)
      (outputs : (n : ℕ) → Fin (counts n) → Matrix (Out n) (Out n) ℂ),
      (∀ n m, errors n m ∈ Set.Icc (0 : ℝ) 1) →
      (∀ n m, QAlgorithms.IsDensityMatrix (outputs n m)) →
      Filter.Tendsto (fun n => ∑ m, uniform m * errors n m) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => ensembleLeakage uniform (outputs n)) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n =>
        (Real.log ((retained (errors n) (outputs n)).card : ℝ) - Real.log (counts n : ℝ)) / n)
        Filter.atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
