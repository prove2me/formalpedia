-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_strongBinding_impliesWeak
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.strongBinding_impliesWeak
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:24:57.28107+00:00
-- url     : https://prove2.me/theorems/4f7e105a-82da-4309-ba9c-479da89fbcbf
-- title:
--   Unnumbered: strong binding implies weak binding
-- statement:
--   Fix any normalized postcommit ccq-state on verifier record $V$, committer record $Z$, and residual quantum register. Let $\varepsilon\ge0$ and assume strong binding in Definition 5.1 for the verifier's fixed acceptance test. One kernel for $B'$ works for every pair of opening strategies, which may differ for bits zero and one. If $p_b$ denotes the unconditional success probability of the strategy for opening $b$, then
--   $$p_b\le\Pr[B'=b]+\Pr[B'=1-b]\varepsilon\quad(b=0,1),\qquad p_0+p_1\le1+\varepsilon.$$
--   All probabilities refer to the same postcommit state. This explains how the strong criterion entails the previously used weak binding property.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 12, Unnumbered: strong binding implies weak binding

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Section 5, p.12: strong binding implies BOTH per-bit inequalities and
p0+p1≤1+epsilon. The two opening strategies may differ, on the SAME postcommit
state and with the SAME B' kernel, chosen before either strategy. -/
theorem strongBinding_impliesWeak {V Z Message I : Type*}
    [Fintype V] [Fintype Z] [Fintype Message] [Fintype I] [DecidableEq I]
    (blocks : (V × Z) → Matrix I I ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (accept : V → Bool → Message → Bool) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbinding : StronglyBinding blocks accept epsilon) :
    ∃ kernel : V → Z → Bool → ℝ, BindingKernel blocks accept epsilon kernel ∧
      ∀ O0 O1 : Opening Z Message I,
        (∀ b : Bool, openingSuccess blocks accept (if b then O1 else O0) b ≤
          bindingMass blocks kernel b + bindingMass blocks kernel (!b)*epsilon) ∧
        openingSuccess blocks accept O0 false + openingSuccess blocks accept O1 true ≤
          1+epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
