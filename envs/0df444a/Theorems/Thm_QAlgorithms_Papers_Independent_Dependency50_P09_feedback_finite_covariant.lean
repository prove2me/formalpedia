-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_feedback_finite_covariant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.feedback_finite_covariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:07:48.789753+00:00
-- url     : https://prove2.me/theorems/2536b2e8-b142-4b86-a386-9fe4aed21c0a
-- title:
--   Corollary 30
-- statement:
--   Let $N$ be a point channel covariant under an input one-design, with the matching unitary output representations. Let $n\ge1$, $0\le\varepsilon<1$, and $\alpha>1$. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Allow free classical feedback for the point channel. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   C_\leftarrow^{n,\varepsilon}(N)\le\widetilde\Upsilon_\alpha(N)+\frac\alpha{n(\alpha-1)}\log_2\frac1{1-\varepsilon}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** One-design averaging is required on every input operator. Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 19, Corollary 30

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

/-- Corollary 30, arXiv:2010.01058v3, PDF pp.19.
One-design averaging is required on every input operator. Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). -/
theorem feedback_finite_covariant {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (N : Superop (Fin a) (Fin d)) (hN : IsChannel N)
    (hcov : HasPointDesign N)
    (n : ℕ) (hn : 0 < n) (epsilon alpha : ℝ)
    (hepsilon : 0 ≤ epsilon ∧ epsilon < 1)
    (halpha : 1 < alpha) :
    feedbackFinite N n epsilon ≤ pointUpsilon (sandwichedD alpha) N +
      (((1 : ℝ)/n : ℝ) : EReal) * penalty alpha epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
