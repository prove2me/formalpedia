-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P88_remark4
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P88.remark4
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:14:47.383649+00:00
-- url     : https://prove2.me/theorems/b1565012-c1fe-4d52-9feb-4312ff1042b4
-- title:
--   Fock projectors distinguish weak operator and trace-norm cone topologies
-- statement:
--   On the full single-mode Fock space, let $P_n=|n\rangle\langle n|$ be the normalized number-state projectors. The weak operator and trace-norm topologies on the positive trace-class cone differ. Specifically,
--
--   $$
--   P_n\xrightarrow{\mathrm{WOT}}0,
--   \qquad
--   (P_n)_{n\ge0}\text{ is not trace-norm Cauchy and has no trace-norm limit}.
--   $$
--
--   Weak operator convergence means $\langle x,P_nx\rangle\to0$ for every Hilbert vector $x$. The limiting operator is zero and therefore lies outside the normalized state space. This gives the counterexample that distinguishes the two cone topologies.
-- source:
--   Asymptotic state transformations of continuous variable resources, arXiv:2010.00044v3, PDF p. 4, II A: Remark4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P88

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P13

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock fockKet fockDyad)

open QAlgorithms.Papers.Independent.Information100.P62 (logTwo)

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.4, Remark 4: the full single-mode Fock projectors tend to zero in
WOT, are not trace-norm Cauchy, and have no trace-norm limit. Consequently the
cone topologies differ. No normalized WOT limit within the state space is asserted. -/
theorem remark4 :
    weakOperatorPositiveTopology (H := Fock) ≠ normPositiveTopology (H := Fock) ∧
    (∀ n : ℕ, IsTraceClass (fockDyad n n) ∧ IsPositive (fockDyad n n) ∧
      (∑' k : ℕ, fockDyad n n (fockKet k) k) = 1) ∧
    (∀ x : Fock, Tendsto (fun n : ℕ => (inner ℂ x (fockDyad n n x)).re)
      atTop (nhds 0)) ∧
    (¬ ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      traceNormValue (fockDyad i i - fockDyad j j) < epsilon) ∧
    (¬ ∃ T : TraceClass Fock, Tendsto
      (fun n : ℕ => traceNormValue (fockDyad n n - T.val)) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P88

end
