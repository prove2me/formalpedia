-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_eb_feedback_extension
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.eb_feedback_extension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:16:20.960763+00:00
-- url     : https://prove2.me/theorems/a8ff24ce-37bd-45fb-b03a-b33738103044
-- title:
--   Unnumbered entanglement-breaking feedback extension
-- statement:
--   Let $N:A\to B'$ be a point channel. Replace each backward classical feedback slot by an arbitrary finite-dimensional, possibly rectangular, entanglement-breaking CPTP channel; optimize over all such slot sequences and codes. Write $C_{\rm EB}^{n,\varepsilon}$ and $\widetilde C_{\rm EB}$ for the resulting maximum-error finite-use and strong-converse capacities. Capacities use adaptive local CPTP interleavings and arbitrary finite local memories, independent initial local states, and no supplied entanglement or shared randomness. The code is chosen before the message distribution. Classical error is the maximum cq trace-distance error over all distributions; randomness transmission (RT) fixes the uniform distribution. Rates are $\log_2M/n$; ordinary capacities take $\inf_{0<\varepsilon<1}\liminf_n$, and strong-converse capacities take $\sup_{0<\varepsilon<1}\limsup_n$. Here $C$ denotes maximum-error classical capacity, $R$ denotes uniform-input randomness-transmission capacity, a tilde denotes the strong-converse version, and a left arrow denotes classical-feedback assistance. A superscript $(n,\varepsilon)$ denotes the finite-use quantity.
--
--   $$
--   C_{\rm EB}^{n,\varepsilon}(N)\le\widehat\Upsilon_\alpha(N)+\frac\alpha{n(\alpha-1)}\log_2\frac1{1-\varepsilon}\quad(n\ge1,\ 0\le\varepsilon<1,\ 1<\alpha\le2),\qquad \widetilde C_{\rm EB}(N)\le\widehat\Upsilon(N).
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
--
--   **Formalization Note** Rectangular EB means every reference-state output is separable; the source measure/prepare decomposition is absorbed into Bob-only preprocessing and Alice-only postprocessing. No formation-potential identity is asserted.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 16, Unnumbered entanglement-breaking feedback extension

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

/-- Unnumbered entanglement-breaking feedback extension, arXiv:2010.01058v3, PDF pp.16.
Rectangular EB means every reference-state output is separable; the source measure/prepare decomposition is absorbed into Bob-only preprocessing and Alice-only postprocessing. No formation-potential identity is asserted. -/
theorem eb_feedback_extension {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (N : Superop (Fin a) (Fin d)) (hN : IsChannel N) :
    (∀ n : ℕ, 0 < n → ∀ epsilon alpha : ℝ, 0 ≤ epsilon → epsilon < 1 →
        1 < alpha → alpha ≤ 2 → ebFinite N n epsilon ≤
          pointUpsilon (geometricD alpha) N +
            (((1 : ℝ)/n : ℝ) : EReal) * penalty alpha epsilon) ∧
      strongCapacityOf (ebFinite N) ≤ pointUpsilon bsD N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
