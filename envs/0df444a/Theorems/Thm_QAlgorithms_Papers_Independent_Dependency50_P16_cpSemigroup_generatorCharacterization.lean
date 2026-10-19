-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_cpSemigroup_generatorCharacterization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.cpSemigroup_generatorCharacterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:38:38.54844+00:00
-- url     : https://prove2.me/theorems/a042f1fa-6727-4275-8bbd-1f1808dcb98c
-- title:
--   Lemma C.2: Generators of CP and quantum dynamical semigroups
-- statement:
--   Let $G$ be a complex-linear map on $M_n(\mathbb C)$, $n\ge2$. The continuous exponential family $e^{tG}$ is a CP semigroup if and only if, for some finite matrices $V_k$ and arbitrary $K$,
--
--   $$G(X)=\sum_kV_kXV_k^*-KX-XK^*.$$
--
--   It is a quantum dynamical semigroup if and only if it is CP and $\operatorname{tr}(G(X))=0$ for every $X$. For any displayed representation, trace annihilation is equivalent to
--
--   $$K=iH_0+\frac12\sum_kV_k^*V_k\quad\text{for some Hermitian }H_0.$$
--
--   Complete positivity is the accepted amplification predicate, and semigroup continuity and composition are explicit. General CP semigroups are not assumed trace preserving.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 30, Lemma C.2: Generators of CP and quantum dynamical semigroups

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.30, Lemma C.2: Generators of CP and quantum dynamical semigroups. Both iff assertions and the actual K representation are retained. G is arbitrary complex-linear, not assumed GKSL before the characterization. Exponentials QAlgorithms.act on finite-dimensional continuous endomorphisms. -/
theorem cpSemigroup_generatorCharacterization {n : ℕ} (hn : 2 ≤ n) (G : Operator n) :
    (cpSemigroup (semigroupEvolution G) ↔ ∃ (r : ℕ) (K : Mat n) (V : Fin r → Mat n),
      G = cpGenerator K V) ∧
    (quantumSemigroup (semigroupEvolution G) ↔ cpSemigroup (semigroupEvolution G) ∧ ∀ X, (G X).trace = 0) ∧
    (∀ (r : ℕ) (K : Mat n) (V : Fin r → Mat n), G = cpGenerator K V →
      ((∀ X, (G X).trace = 0) ↔ ∃ H : Mat n, H.IsHermitian ∧
        K = Complex.I • H + (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
