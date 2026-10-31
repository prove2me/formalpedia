-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P22_q_identities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P22.q_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:50:47.484992+00:00
-- url     : https://prove2.me/theorems/c23083b8-52b7-4e76-b0be-a38ba69807a0
-- title:
--   Ordered Q-factor sum symmetry and square-root identity
-- statement:
--   Fix an integer $n\ge4$ and any real $\alpha$. For $0\le a<b<c<d\le n-1$, put $s_{uv}=\sin(\pi(v-u)/n)$ and define
--   $$Q_0=\frac{s_{bd}s_{ac}}{s_{ab}s_{cd}s_{ad}s_{bc}},\quad Q_1=\frac{s_{ad}s_{bc}}{s_{ab}s_{cd}s_{bd}s_{ac}},\quad Q_2=\frac{s_{ab}s_{cd}}{s_{bd}s_{ac}s_{ad}s_{bc}}.$$
--   All three factors are positive. They obey the pointwise identity
--   $$\sqrt{Q_0}=\sqrt{Q_1}+\sqrt{Q_2}.$$
--   After fixing $a=0$, their real powers obey
--   $$\sum_{1\le b<c<d\le n-1}Q_1(0,b,c,d)^{2\alpha}=\sum_{1\le b<c<d\le n-1}Q_2(0,b,c,d)^{2\alpha}.$$
--   The powered identity is at the level of the sums, not a termwise equality. These identities simplify the four-point sector coefficients.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory II, arXiv:1011.5482v1, PDF p. 19, §5.4, equations (91)–(98)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P22

open scoped BigOperators Topology

open Filter MeasureTheory

/-- PDF pp. 18–19, (91)–(98): powered equality after summing with j_1=0;
square-root identity termwise on the ordered domain. No permutation claim
outside that domain is assumed. -/
theorem q_identities (n : ℕ) (hn : 4 ≤ n) (alpha : ℝ) :
    reducedQSum n alpha 1 = reducedQSum n alpha 2 ∧
    ∀ a b c d : ℕ, a < b → b < c → c < d → d ≤ n - 1 →
      (∀ r : Fin 3, 0 < qFactor n a b c d r) ∧
      Real.sqrt (qFactor n a b c d 0) =
        Real.sqrt (qFactor n a b c d 1) + Real.sqrt (qFactor n a b c d 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P22

end
