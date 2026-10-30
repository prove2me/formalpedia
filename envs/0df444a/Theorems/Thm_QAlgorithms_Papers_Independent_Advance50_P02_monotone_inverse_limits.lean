-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_monotone_inverse_limits
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.monotone_inverse_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:26:24.251789+00:00
-- url     : https://prove2.me/theorems/4e7abb2c-498f-419c-8fe3-55f39a290f16
-- title:
--   Monotone generalized inverse and limit identities
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $g_n:\mathbb R\to\mathbb R$ be nondecreasing, with no continuity or boundedness requirement, and define $f_n(a)=\sup\{R:g_n(R)\le a\}$ in the extended reals. For every real $\varepsilon$,
--   $$\sup_{\limsup a_n\le\varepsilon}\liminf_n f_n(a_n)=\sup\{R:\limsup_n g_n(R)\le\varepsilon\},$$
--   $$\sup_{\liminf a_n<\varepsilon}\liminf_n f_n(a_n)=\sup\{R:\liminf_n g_n(R)<\varepsilon\}.$$
--   The sequences $a_n$ range over all real sequences. Empty and unbounded optimizations retain their infinite endpoints. These identities connect one-shot inverse quantities to asymptotic thresholds.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 22, Lemma 18: monotone inverse/limit identities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Lemma 18, PDF p.22, (39),(40): no continuity or boundedness assumption. -/
theorem monotone_inverse_limits (g : ℕ → ℝ → ℝ) (hg : ∀ n, Monotone (g n)) (e : ℝ) :
    inverseRate g e false = thresholdRate g e false ∧
    inverseRate g e true = thresholdRate g e true := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
