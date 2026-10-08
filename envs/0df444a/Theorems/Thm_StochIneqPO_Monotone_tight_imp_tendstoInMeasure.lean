-- Prove2me | Theorems.Thm_StochIneqPO_Monotone_tight_imp_tendstoInMeasure
-- name    : StochIneqPO.Monotone.tight_imp_tendstoInMeasure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:28:05.264037+00:00
-- url     : https://prove2.me/theorems/5048b9bc-6134-4cea-8c9c-2b54e24cb359
-- title:
--   Proof of Theorem 6, p. 908 — a tight nondecreasing random sequence converges in probability
-- statement:
--   Let $E$ be a complete separable metric space (a Polish space with metric $d$) endowed with a closed partial ordering $\le$ (the set $\{(x,y): x\le y\}$ is closed in $E\times E$) and its Borel $\sigma$-algebra. Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $X_1,X_2,\dots:\Omega\to E$ be measurable with
--
--   $$
--   X_1(\omega)\le X_2(\omega)\le\cdots\qquad\text{for every }\omega\in\Omega .
--   $$
--
--   If the family of distributions $\{P_i=\mu\circ X_i^{-1} : i\ge1\}$ is tight, then $(X_i)$ converges in probability: there is a measurable $Y:\Omega\to E$ with
--
--   $$
--   \mu\{\omega : d(X_i(\omega),Y(\omega))\ge\varepsilon\}\;\longrightarrow\;0\qquad(i\to\infty)\quad\text{for every }\varepsilon>0 .
--   $$
--
--   This is the implication (i) $\Rightarrow$ (iii) of Theorem 6, the substantial step of its first part; together with the standard implications (iii) $\Rightarrow$ (ii) $\Rightarrow$ (i) it gives the equivalence of tightness, weak convergence and convergence in probability for monotone sequences.
--
--   **Formalization Note** The closed partial ordering is Mathlib's `OrderClosedTopology`. Separability is stated as second countability, which is equivalent for metric spaces. The monotonicity $X_1\le X_2\le\cdots$ is required for every $\omega$, as in the paper; an almost sure version is equivalent after modifying the $X_i$ on a null set. The sequence index starts at $0$ in Lean.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proof of Theorem 6, (i) ⇒ (iii), p. 908 (PDF p. 10)

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes

namespace StochIneqPO.Monotone

open MeasureTheory

theorem tight_imp_tendstoInMeasure {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (htight : LawsTight μ X) :
    ConvergesInProbability μ X := by sorry

end StochIneqPO.Monotone
