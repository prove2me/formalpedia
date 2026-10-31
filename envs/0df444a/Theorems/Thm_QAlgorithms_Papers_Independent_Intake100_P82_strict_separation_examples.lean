-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_strict_separation_examples
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.strict_separation_examples
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:27:42.440115+00:00
-- url     : https://prove2.me/theorems/d002736b-be37-458a-9c35-cac65f90c04b
-- title:
--   Remark 6.6: strict separation of additive classes
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   The spatially constant sequence $G_n(x)=\log n$ is bounded Borel at each positive time, weakly almost additive, and not almost additive with any fixed error constant. The spatially constant sequence
--   $$H_n(x)=\begin{cases}\sqrt n,&n\text{ even},\\0,&n\text{ odd}\end{cases}$$
--   is AA and is not weakly almost additive. Both sequences are equivalent to zero: $\|G_n\|_\infty/n\to0$ and $\|H_n\|_\infty/n\to0$. These are the two explicit strict separations; the cited later resolution of the additive-representative question is not asserted here.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 43, Remark 6.6: strict separation of additive classes

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Remark 6.6, arXiv:1712.05167v3, PDF p.43. Both explicit strict-separation
examples and both equivalences to zero. No claim to prove the cited Cun20 result. -/
theorem strict_separation_examples (phi : M → M) (hphi : Continuous phi) :
    BorelSequence (logTimePotential : ℕ → M → ℝ) ∧
    WeakAlmostAdditive phi logTimePotential ∧ ¬ AlmostAdditive phi logTimePotential ∧
    BorelSequence (alternatingRootPotential : ℕ → M → ℝ) ∧
    AsymptoticallyAdditive phi alternatingRootPotential ∧
    ¬ WeakAlmostAdditive phi alternatingRootPotential ∧
    EquivalentPotentials (logTimePotential : ℕ → M → ℝ) (fun _ _ => 0) ∧
    EquivalentPotentials (alternatingRootPotential : ℕ → M → ℝ) (fun _ _ => 0) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
