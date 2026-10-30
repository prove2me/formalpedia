-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_private_finiteBlock_error
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.private_finiteBlock_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:06:15.264228+00:00
-- url     : https://prove2.me/theorems/65dd5127-29d3-456a-928e-9a07195b1276
-- title:
--   Lemma IV.2: finite-block private error lower bound
-- statement:
--   Let $T$ be a quantum channel in positive finite dimensions and let $1<\alpha<\infty$. Consider a private-state generation code with $m\ge1$ actual channel uses, separable initial state, arbitrary finite local workspace, and two-way classical communication. Its target private state has key dimension $2^k$ for an integer $k\ge0$ and equal shield dimensions. If its actual error $\epsilon=\tfrac12\|\phi-\gamma\|_1$ is positive, then
--
--   $$\epsilon\ge1-2^{-\frac{\alpha-1}{2\alpha}(k-mE_{\max}(T))}.$$
--
--   The output $\phi$ is evaluated from the code and $\gamma$ is its private-state target. The channel max-relative entanglement is finite and expressed in bits.
--
--   This is the finite-block estimate underlying the private strong converse.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 13, Lemma IV.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Lemma IV.2, PDF pp.13--14: positive ACTUAL error and coefficient
(alpha-1)/(2 alpha). Emax is finite for finite-dimensional channels (p.5),
so its toReal here never converts an infinite physical value to zero. -/
theorem private_finiteBlock_error (T : Superop I J) (hT : IsChannel T)
    (alpha : ℝ) (halpha : 1 < alpha) (code : TwoWayGenerationCode T true)
    (herror : 0 < generationCodeError code) :
    1 - (2 : ℝ) ^ (-((alpha - 1) / (2 * alpha)) *
      ((code.key : ℝ) - (code.uses : ℝ) * (channelEMax T).toReal)) ≤ generationCodeError code := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
