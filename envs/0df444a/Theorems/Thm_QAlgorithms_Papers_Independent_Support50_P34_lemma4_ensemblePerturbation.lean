-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma4_ensemblePerturbation
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma4_ensemblePerturbation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:38:50.379974+00:00
-- url     : https://prove2.me/theorems/fc166533-0aaa-4c03-838f-3d7cc28200cc
-- title:
--   Lemma 4: perturbation of countable bounded-rank ensembles
-- statement:
--   Fix $k\ge1$ and a countable ensemble $(\pi_i,\sigma_i)_{i\ge1}$ of states of rank at most $k$, with average $\rho$. If $\rho_n\to\rho$ in trace norm, there are ensembles $(\pi_i^n,\sigma_i^n)_{i\ge1}$ of states of rank at most $k$, indexed by the same countable set, such that
--
--   $$\rho_n=\sum_i\pi_i^n\sigma_i^n,\qquad \pi_i^n\to\pi_i,\qquad \pi_i>0\Longrightarrow\sigma_i^n\to\sigma_i.$$
--
--   All operator averages and state limits use trace norm. No convergence of component states is required at a zero limiting weight. This is the rank-preserving ensemble perturbation result.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 8, Lemma 4: perturbation of countable bounded-rank ensembles

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*}

section Statements

variable [hsep : TopologicalSpace.SeparableSpace H] [hI : Countable I]

include hsep hI

/-- Lemma 4, arXiv:0904.1963v3, PDF p.8: perturbation on the same countable index set;
component convergence is required only at a positive limiting weight. -/
theorem lemma4_ensemblePerturbation (b : HilbertBasis I ℂ H) (k : ℕ) (hk : 0 < k)
    (w : ℕ → ℝ) (s : ℕ → QuantumState b) (rho : QuantumState b)
    (he : StateEnsemble b w s rho) (hs : ∀ i, s i ∈ rankStates b k)
    (u : ℕ → QuantumState b) (hu : Tendsto u atTop (nhds rho)) :
    ∃ (wn : ℕ → ℕ → ℝ) (sn : ℕ → ℕ → QuantumState b),
      (∀ n, StateEnsemble b (wn n) (sn n) (u n)) ∧
      (∀ n i, sn n i ∈ rankStates b k) ∧
      (∀ i, Tendsto (fun n => wn n i) atTop (nhds (w i))) ∧
      (∀ i, 0 < w i → Tendsto (fun n => sn n i) atTop (nhds (s i))) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
