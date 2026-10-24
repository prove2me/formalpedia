-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_depolarizingCapacityLeadingAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P31.depolarizingCapacityLeadingAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:33:12.89196+00:00
-- url     : https://prove2.me/theorems/0bf4dde2-d1da-404d-b595-649f364d4a09
-- title:
--   Leading capacity additivity in weak and strong depolarization
-- statement:
--   Fix $n\ge1$ and positive dimensions $d_i$. Let $q_i(t)$ be real parameter functions such that there are constants $0<a\le b$ for which, for all sufficiently small $t>0$ and every $i$,
--   $$
--   0<q_i(t)<1,\qquad at\le q_i(t)\le bt.
--   $$
--   Write $D_{d,p}(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I_d$, and let $C$ be the unregularized one-step Holevo maximum in natural units. Both regimes satisfy
--   $$
--   \begin{aligned}
--   C\!\left(\bigotimes_i D_{d_i,q_i(t)}\right)-\sum_i C(D_{d_i,q_i(t)})
--    &=o(t\log t),\\
--   C\!\left(\bigotimes_i D_{d_i,1-q_i(t)}\right)-\sum_i C(D_{d_i,1-q_i(t)})
--    &=o(t^2)
--   \end{aligned}
--   \qquad(t\downarrow0).
--   $$
--   The first line is weak depolarization; the second is strong depolarization and keeps the second-order capacity scale. Comparable parameters need not be equal, smooth, or exact scalar multiples of $t$. This precisely expresses the source's leading capacity-additivity proposition in both regimes.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 10, §5, Proposition: weak and strong depolarization

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.10–11, Proposition: leading capacity additivity in BOTH comparable-scale
regimes. Weak error is o(t log t); strong error is o(t squared), retaining the
second-order term. Parameters need not be equal or exact rays. -/
theorem depolarizingCapacityLeadingAdditivity {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (q : ℝ → Fin n → ℝ) (hq : ComparableScale q) :
    ((fun t => holevoQuantity (depolarizingProduct d hd (q t)) -
        ∑ i, holevoQuantity (QuditFidelity.depolarizingMap (d i) (hd i) (q t i)))
      =o[zeroRight] (fun t => t * Real.log t)) ∧
    ((fun t => holevoQuantity (depolarizingProduct d hd (fun i => 1 - q t i)) -
        ∑ i, holevoQuantity (QuditFidelity.depolarizingMap (d i) (hd i) (1 - q t i)))
      =o[zeroRight] (fun t => t ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
