-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_theorem_3_2
-- name    : PrivateRelease.NetMechanism.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:36.868759+00:00
-- url     : https://prove2.me/theorems/5b07385b-3f43-4562-8506-17e6b9ab7ad0
-- title:
--   Theorem 3.2 [MT07] — the exponential mechanism is ε-differentially private
-- statement:
--   Let $X$ be a finite data universe, $n$ an input size, $R$ a finite nonempty range and $q:X^n\times R\to\mathbb R$ a quality score with $GS_q>0$. For every $\varepsilon>0$ the exponential mechanism $M_E(\cdot,q,R)$ is $\varepsilon$-differentially private: for all inputs $z,z'\in X^n$ differing in one entry and every set $S$ of outputs,
--   $$
--   \Pr[M_E(z,q,R)\in S]\le e^{\varepsilon}\,\Pr[M_E(z',q,R)\in S] ,
--   $$
--   and each output law is a probability distribution on $R$.
--
--   This is the privacy guarantee of McSherry and Talwar's exponential mechanism, of which the Net mechanism is an instance.
--
--   **Formalization Note** The hypothesis $GS_q>0$ is where the paper's formula $\exp(\varepsilon q/(2GS_q))$ is defined. Neighbours differ in exactly one entry. The probability-measure clause is stated because the platform's privacy predicate alone does not require it.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 8, Theorem 3.2 (citing McSherry–Talwar 2007)

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

namespace PrivateRelease.NetMechanism

open MeasureTheory

/-- Theorem 3.2 ([MT07], p. 8): the exponential mechanism `M_E(·, q, R)` over a finite nonempty
range `R`, with a quality score of positive sensitivity `GS_q`, preserves ε-differential
privacy; each of its output laws is a probability measure. -/
theorem theorem_3_2 {X O : Type} [Fintype X] [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (hR : R.Nonempty) (hq : 0 < scoreSens R q)
    (hε : 0 < ε) :
    PrivLearn.Generic.IsDP (expMech R q ε) ε ∧
      ∀ z : Fin n → X, IsProbabilityMeasure (expMech R q ε z) := by sorry

end PrivateRelease.NetMechanism
