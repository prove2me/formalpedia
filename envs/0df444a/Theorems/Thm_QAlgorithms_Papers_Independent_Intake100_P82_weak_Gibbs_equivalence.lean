-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_weak_Gibbs_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.weak_Gibbs_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:19:04.797876+00:00
-- url     : https://prove2.me/theorems/914e3183-46c1-46f3-bfe8-bdd3d32cf56c
-- title:
--   Remark 4.2: Gibbs potentials and equivalence
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G,\mathcal H\in\mathcal A(M)$ and $P\in\mathcal P(M)$. If $P$ is weak Gibbs for both sequences, then
--   $$(G_n-np(\mathcal G))\sim(H_n-np(\mathcal H)).$$
--   Conversely, if $\mathcal G\sim\mathcal H$, then $P$ is weak Gibbs for $\mathcal G$ exactly when it is weak Gibbs for $\mathcal H$. Equivalence means vanishing normalized uniform difference. A common Gibbs law does not force unnormalized equivalence before subtracting pressures.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 31, Remark 4.2: Gibbs potentials and equivalence

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

/-- Remark 4.2, arXiv:1712.05167v3, PDF p.31. A common weak Gibbs measure
implies equivalence AFTER subtracting pressures. Source equivalence conversely
preserves the weak Gibbs property. -/
theorem weak_Gibbs_equivalence (phi : M → M) (hphi : Continuous phi)
    (G H : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (hH : AsymptoticallyAdditive phi H) (P : ProbabilityMeasure M) :
    (WeakGibbs phi G P → WeakGibbs phi H P →
      EquivalentPotentials (fun n x => G n x - (n : ℝ) * (separatedSetPressure phi G).toReal)
        (fun n x => H n x - (n : ℝ) * (separatedSetPressure phi H).toReal)) ∧
    (EquivalentPotentials G H → (WeakGibbs phi G P ↔ WeakGibbs phi H P)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
