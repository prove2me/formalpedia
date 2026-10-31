-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_kernel_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.kernel_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:43:45.292818+00:00
-- url     : https://prove2.me/theorems/9dcf907f-cc64-456e-bd08-0ef51222f0af
-- title:
--   Lemma in Theorem 3 proof: kernel bound
-- statement:
--   For $p,q\in[0,1]$, define $g(p,q)=0$ if either argument is zero, $g(p,p)=1$ if $p>0$, and otherwise $g(p,q)=\sqrt{pq}\ln(q/p)/(q-p)$. Then
--
--   $$0\le g(p,q)\le1.$$
--
--   This is the kernel bound used in the pure-state minimizer argument, with its diagonal and zero boundaries resolved explicitly.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 13, Lemma in Theorem 3 proof: kernel bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma, PDF p.13, Eqs.(27)–(30): zero weights and the diagonal use their defined limits. -/
theorem kernel_bound (p q : ℝ) (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    0 ≤ kernelG p q ∧ kernelG p q ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
