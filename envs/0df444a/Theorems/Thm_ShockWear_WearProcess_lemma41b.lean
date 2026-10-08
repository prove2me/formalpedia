-- Prove2me | Theorems.Thm_ShockWear_WearProcess_lemma41b
-- name    : ShockWear.WearProcess.lemma41b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:49:45.674455+00:00
-- url     : https://prove2.me/theorems/f1945620-1666-41f0-ae58-ab381f8d23a3
-- title:
--   Lemma 4.1b — $[P\{X_1+\dots+X_k\le x\}]^{1/k}$ is decreasing in $k$ for dependent damages satisfying (4.3)–(4.5)
-- statement:
--   Let $X_1,X_2,\dots$ be nonnegative random variables on a probability space whose joint distribution satisfies the dependent-damage conditions (4.3), (4.4) and (4.5): the conditional distribution of $X_{k+1}$ given $X_1,\dots,X_k$ depends only on $Z_k=X_1+\dots+X_k$ (with $Z_0=0$), and, through a version $\kappa_k$ of it, $P\{X_{k+1}\le u\mid Z_k=z\}$ is decreasing in $z\ge0$ and decreasing in $k$ at every fixed $z\ge0$. Then for every real $x$,
--
--   $$
--   \big[P\{X_1+\dots+X_k\le x\}\big]^{1/k}\quad\text{is decreasing in } k=1,2,\dots,
--   $$
--
--   that is, $[P\{Z_k\le x\}]^{1/k}\le[P\{Z_j\le x\}]^{1/j}$ whenever $1\le j\le k$.
--
--   In the shock model this says that $\bar P_k=P\{Z_k\le x\}$, the probability of surviving $k$ shocks with threshold $x$, has $\bar P_k^{1/k}$ decreasing; it is the discrete-time step behind Corollary 4.2 (4.7b) and Theorem 4.10.
--
--   **Formalization Note** The conditions are the structure `IsDamageSeq` with an explicit version $\kappa$ of the conditional laws (the paper states the monotonicity for "$P\{X_k\le u\mid Z_{k-1}=z\}$", which is defined only a.e.; we state it for a version). Lean's `X i` is the paper's $X_{i+1}$ and `psum X k` is $Z_k$. Nonnegativity is almost sure. The power $1/k$ is a real exponent.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 637, Lemma 4.1b (conditions (4.3)–(4.5), p. 636)

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem lemma41b {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (X : ℕ → Ω → ℝ) (κ : ℕ → Kernel ℝ ℝ) (hX : IsDamageSeq pr X κ) (x : ℝ) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    (pr {ω | psum X k ω ≤ x}).toReal ^ (1 / (k : ℝ)) ≤
      (pr {ω | psum X j ω ≤ x}).toReal ^ (1 / (j : ℝ)) := by sorry

end ShockWear.WearProcess
