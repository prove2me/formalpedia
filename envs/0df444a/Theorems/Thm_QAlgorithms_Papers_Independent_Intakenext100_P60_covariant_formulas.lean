-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_covariant_formulas
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.covariant_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:55:26.734985+00:00
-- url     : https://prove2.me/theorems/12b0e002-f8bc-4e28-a504-1952bb0897e4
-- title:
--   §7, equations (16)–(18): capacity, normalized projector and minimizing orbits
-- statement:
--   Let $G$ be a compact topological group with continuous unitary representations $V$ on a nonzero finite-dimensional space $K$ and $U$ on a nonzero finite-dimensional output space $B$, both irreducible. Identify $K$ with the range of an isometry $W:K\longrightarrow A\otimes B$. Assume, for every $g\in G$ and every operator $X$ on $K$,
--   $$\operatorname{Tr}_A(WV_gXV_g^\dagger W^\dagger)=U_g\operatorname{Tr}_A(WXW^\dagger)U_g^\dagger.$$
--   Let $T(X)=\operatorname{Tr}_A(WXW^\dagger)$, $P=WW^\dagger$, $\tau=P/\operatorname{Tr}P$, and $m=\min_{\|x\|=1} E(Wx)$, where $E$ is pure-state marginal entropy. An arbitrary ambient environment can be compressed to the finite component span without changing any supported state or entanglement value. The group action need not factor across the two parties.
--
--   The minimum defining $m$ is attained, and
--   $$C(T)=\log_2\dim B-E_f(\tau),\qquad E_f(\tau)=m.$$
--   For every unit minimizing seed $x$, all orbit vectors $WV_gx$ have the same entanglement $m$, and every density matrix in the convex hull of their pure projectors has formation $m$. The convex hull is a set of mixtures of projectors, not the linear span of their supports. These formulas express the channel capacity and the formation of its normalized dilation projector through one pure-state minimum.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 11, §7, equations (16)–(18): capacity, normalized projector and minimizing orbits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF p.11, (16)--(18): capacity, normalized-projector formation, attained pure
minimum, entropy preservation on minimizing orbits, and their convex mixtures.
Both actions are irreducible; the product-case hypothesis is deliberately absent. -/
theorem covariant_formulas {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] {a b k : ℕ} (D : CovariantData G a b k) :
    dilationCapacity D.W = Real.logb 2 b - formation (projectorState D) ∧
    formation (projectorState D) = minimumEntanglement D ∧
    (∃ v : EuclideanSpace ℂ (Fin k), ‖v‖ = 1 ∧
      pureEntropyBits (embedded D.W v) = minimumEntanglement D) ∧
    (∀ v : EuclideanSpace ℂ (Fin k), ‖v‖ = 1 →
      pureEntropyBits (embedded D.W v) = minimumEntanglement D →
      (∀ g : G, pureEntropyBits (embedded D.W (act (D.V g) v)) =
        pureEntropyBits (embedded D.W v)) ∧
      (∀ rho : Op (Fin a × Fin b), IsDensityMatrix rho → rho ∈ minimizingProjectorHull D v →
        formation rho = minimumEntanglement D)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
