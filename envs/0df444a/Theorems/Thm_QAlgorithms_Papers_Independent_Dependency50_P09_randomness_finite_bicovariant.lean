-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_randomness_finite_bicovariant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.randomness_finite_bicovariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:06:23.987983+00:00
-- url     : https://prove2.me/theorems/18edaa9c-994d-4110-97d7-4c9593eb2e6c
-- title:
--   Corollary 28
-- statement:
--   Let $N$ be a bipartite channel covariant under two independent input one-designs, with the matching unitary output representations. Let $n\ge1$, $0\le\varepsilon<1$, and $\alpha>1$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   R^{n,\varepsilon}(N)\le\widetilde\Upsilon_\alpha(N)+\frac\alpha{n(\alpha-1)}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** One-design averaging is required on every input operator. Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 18, Corollary 28

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Corollary 28, arXiv:2010.01058v3, PDF pp.18.
One-design averaging is required on every input operator. Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). -/
theorem randomness_finite_bicovariant {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (N : Superop (Fin a × Fin b) (Fin c × Fin d)) (hN : IsChannel N)
    (hcov : HasBiDesign N)
    (n : ℕ) (hn : 0 < n) (epsilon alpha : ℝ)
    (hepsilon : 0 ≤ epsilon ∧ epsilon < 1)
    (halpha : 1 < alpha) :
    finiteCapacity N n epsilon true ≤ upsilon (sandwichedD alpha) N +
      (((1 : ℝ)/n : ℝ) : EReal) * penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
