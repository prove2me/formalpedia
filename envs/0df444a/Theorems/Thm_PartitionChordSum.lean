-- Prove2me | Theorems.Thm_PartitionChordSum
-- name    : PartitionChordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:24.496256+00:00
-- url     : https://prove2.me/theorems/90d4cdbc-732b-5645-91d1-4d4fe0c50093
-- title:
--   Partition Chord Sum: Partition Chord Sum
-- statement:
--   Paper eqs. (RiemannStieltjesSum)+(mSumBound) (paper.tex 1740-1754), the shared preliminary of
--   Lemma A.2: for the uniform `m`-piece partition `s_i = i \cdot length(g)/m` of a curve `g` and an
--   arbitrary choice of sample points `u i \in [s_i, s_{i+1}]`, the current `[[g]](f,\pi)` differs
--   from the Riemann-Stieltjes sum `\sum_i f(g(u_i)) (\pi(g(s_{i+1})) - \pi(g(s_i)))` by at most
--   `Lip(f) Lip(\pi) length(g)^2 / m`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PartitionChordSum.lean#L13-L106
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PartitionChordSum.lean#L13-L106

import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PartitionChordSum
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false

theorem PartitionChordSum {E : Type*} [MetricSpace E] (g : Curve E) (ω : Form1 E) (m : ℕ)
    (hm : 1 ≤ m) (u : ℕ → ℝ)
    (hu : ∀ i, i < m → (i : ℝ) * g.len / m ≤ u i ∧ u i ≤ ((i : ℝ) + 1) * g.len / m) :
    |curveCurrent g ω
        - ∑ i ∈ Finset.range m,
            ω.f (g.toFun (u i))
              * (ω.pi (g.toFun (((i : ℝ) + 1) * g.len / m))
                  - ω.pi (g.toFun ((i : ℝ) * g.len / m)))|
      ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * g.len ^ 2 / m := by sorry
