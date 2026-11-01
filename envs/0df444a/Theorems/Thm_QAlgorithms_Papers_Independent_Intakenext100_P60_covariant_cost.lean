-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_covariant_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.covariant_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:56:05.178551+00:00
-- url     : https://prove2.me/theorems/6068e570-9ac9-4350-9cfa-924e8a488493
-- title:
--   §7, equation (19): extension of projector cost equality to minimizing orbit mixtures
-- statement:
--   Let $G$ be a compact topological group with continuous unitary representations $V$ on a nonzero finite-dimensional space $K$ and $U$ on a nonzero finite-dimensional output space $B$, both irreducible. Identify $K$ with the range of an isometry $W:K\longrightarrow A\otimes B$. Assume, for every $g\in G$ and every operator $X$ on $K$,
--   $$\operatorname{Tr}_A(WV_gXV_g^\dagger W^\dagger)=U_g\operatorname{Tr}_A(WXW^\dagger)U_g^\dagger.$$
--   Let $T(X)=\operatorname{Tr}_A(WXW^\dagger)$, $P=WW^\dagger$, $\tau=P/\operatorname{Tr}P$, and $m=\min_{\|x\|=1} E(Wx)$, where $E$ is pure-state marginal entropy. An arbitrary ambient environment can be compressed to the finite component span without changing any supported state or entanglement value. The group action need not factor across the two parties.
--
--   Assume in addition $E_c(\tau)=E_f(\tau)$. Fix a unit vector $x$ attaining $m$, and let $\rho$ be any density matrix in the convex hull of $\{|WV_gx\rangle\langle WV_gx|:g\in G\}$. Then
--   $$E_c(\rho)=E_f(\rho)=m,\qquad E_f(\rho^{\otimes n})=nm\quad(n\ge1).$$
--   This extends the given projector cost equality to mixtures of a minimizing orbit; the projector equality is a hypothesis, not a consequence asserted for every group action.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 12, §7, equation (19): extension of projector cost equality to minimizing orbit mixtures

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

/-- PDF pp.11--12, (19): cost equality and positive-copy formation additivity for
minimizing-orbit mixtures, conditional on cost=formation for the normalized projector.
The undefined rho_0 on p.12 is the preceding minimizing pure projector.
No local implementability of V is assumed. -/
theorem covariant_cost {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] {a b k : ℕ} (D : CovariantData G a b k)
    (hcost : formationCostBits (projectorState D) = formation (projectorState D))
    (v : EuclideanSpace ℂ (Fin k)) (hv : ‖v‖ = 1)
    (hmin : pureEntropyBits (embedded D.W v) = minimumEntanglement D)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) (horbit : rho ∈ minimizingProjectorHull D v) :
    formationCostBits rho = minimumEntanglement D ∧ formation rho = minimumEntanglement D ∧
      (∀ n : ℕ, 0 < n → formation (groupedPower rho n) = n * minimumEntanglement D) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
