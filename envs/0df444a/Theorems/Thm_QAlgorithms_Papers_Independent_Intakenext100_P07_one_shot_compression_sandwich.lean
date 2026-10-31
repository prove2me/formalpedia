-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_one_shot_compression_sandwich
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.one_shot_compression_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:38:21.148817+00:00
-- url     : https://prove2.me/theorems/af4297d2-82c4-4747-8cef-ba9fb3f07996
-- title:
--   §1.2 (1.6)–(1.7): one-shot compression sandwich
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet $X$. A code consists of an encoder into an alphabet of $m\ge1$ symbols and a decoder, and its error is the probability of recovering the wrong source symbol. Logs are binary, and $H(p)$ is Shannon entropy. Introductory smooth max-entropy minimizes the order-$1/2$ Rényi entropy over normalized probability laws within variational distance $\varepsilon$.
--
--   Let p be a finite probability source and 0<epsilon<1. For every 0<delta<epsilon, a code exists whenever log2 m is at least the variation-smoothed order-1/2 entropy at epsilon-delta plus log2(1/delta). Every epsilon-error code obeys the converse lower bound. The least positive feasible alphabet size m*(epsilon) exists and obeys the displayed sandwich.
--
--   $$
--   H_{\max}^{\varepsilon}(p)\le\log_2m^*(\varepsilon)\le\inf_{0<\delta<\varepsilon}\left\lceil H_{\max}^{\varepsilon-\delta}(p)+\log_2\frac1\delta\right\rceil.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 13, §1.2 (1.6)–(1.7): one-shot compression sandwich

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#1.smoothcompression
Equations (1.6)-(1.7), PDF pp.13-14. The plan's rounding concern is discharged by an explicit power-of-two candidate:
m=2^ceil(H+log(1/d)). The minimum over all alphabet sizes is at most this candidate;
no power-of-two restriction is imposed on the optimum. Independent moderation pending. -/
theorem one_shot_compression_sandwich [Nonempty X] (p : X → ℝ) (hp : paperProbability p)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    (∀ d : ℝ, 0 < d → d < e → ∀ m : ℕ, 0 < m →
      introSmoothMax p (e-d)+Real.logb 2 (1/d) ≤ Real.logb 2 m →
      ∃ c : paperSourceCode X m, paperCodeError p c ≤ e) ∧
    (∀ m : ℕ, 0 < m → ∀ c : paperSourceCode X m, paperCodeError p c ≤ e → introSmoothMax p e ≤ Real.logb 2 m) ∧
    (0 < optimalCardinality p e ∧ ∃ c : paperSourceCode X (optimalCardinality p e), paperCodeError p c ≤ e) ∧
    introSmoothMax p e ≤ Real.logb 2 (optimalCardinality p e) ∧
    Real.logb 2 (optimalCardinality p e) ≤ sInf {v : ℝ | ∃ d : ℝ, 0 < d ∧ d < e ∧
      v = (Nat.ceil (introSmoothMax p (e-d)+Real.logb 2 (1/d)):ℝ)} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
