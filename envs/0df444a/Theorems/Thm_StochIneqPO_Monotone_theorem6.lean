-- Prove2me | Theorems.Thm_StochIneqPO_Monotone_theorem6
-- name    : StochIneqPO.Monotone.theorem6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:28:32.411468+00:00
-- url     : https://prove2.me/theorems/baa3eb77-cd56-4add-b826-f0df34401720
-- title:
--   Theorem 6 — for nondecreasing random sequences, tight ⇔ weakly convergent ⇔ convergent in probability; a.s. convergence is equivalent for all such sequences iff (17)
-- statement:
--   Let $E$ be a Polish space with metric $d$ (a complete separable metric space), endowed with a closed partial ordering $\le$ and its Borel $\sigma$-algebra.
--
--   **First part.** Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $X_1,X_2,\dots:\Omega\to E$ be random variables with $X_1\le X_2\le\cdots$ (pointwise on $\Omega$), with distributions $P_i=\mu\circ X_i^{-1}$. Then the following conditions are equivalent:
--
--   1. the family $\{P_i : i\ge1\}$ is tight;
--   2. $\{P_i : i\ge1\}$ converges weakly to a probability measure;
--   3. $\{X_i : i\ge1\}$ converges in probability.
--
--   **Second part.** The condition
--
--   4. $\{X_i : i\ge 1\}$ converges almost surely
--
--   is also equivalent (to 3, and hence to 1 and 2) for all nondecreasing sequences $\{X_i\}$ on all probability spaces if and only if $E$ satisfies condition (17):
--
--   $$
--   x_n\le y_n\le x_{n+1}\ (n\ge1),\quad x_n\to z\in E\quad\Longrightarrow\quad y_n\to z .
--   $$
--
--   The theorem says that for monotone sequences in an ordered Polish space the weak and the in-probability modes of convergence coincide, so that tightness of the marginal laws alone already yields a limiting random variable; and it characterises, by an intrinsic property of the ordered space, when the strongest mode, almost sure convergence, joins them.
--
--   **Formalization Note** The closed partial ordering is Mathlib's `OrderClosedTopology`; separability is second countability. The modes (i)–(iv) are those of the definition file `ConvergenceModes` (weak convergence through integrals of bounded continuous functions against a probability-measure limit; convergence in probability to a measurable limit). The first part is stated for probability spaces in an arbitrary universe; in the second part the quantifier over probability spaces ranges over `Type`, and "(iv) is also equivalent" is encoded as "(iv) $\Leftrightarrow$ (iii)" for every pointwise nondecreasing sequence of measurable maps on every such space; the quantifier over all sequences is essential, since for one fixed sequence the "only if" direction is false. Sequences are indexed from $0$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 6 (with condition (17)), p. 908 (PDF p. 10)

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory

universe u

theorem theorem6 {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E] :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        List.TFAE [LawsTight μ X, LawsConvergeWeakly μ X, ConvergesInProbability μ X]) ∧
    (Regular17 E ↔
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → E), (∀ i, Measurable (X i)) → (∀ ω, Monotone fun i => X i ω) →
        (ConvergesAS μ X ↔ ConvergesInProbability μ X)) := by sorry

end StochIneqPO.Monotone
