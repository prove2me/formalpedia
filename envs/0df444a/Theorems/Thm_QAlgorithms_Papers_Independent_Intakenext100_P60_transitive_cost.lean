-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_transitive_cost
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.transitive_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:57:04.394107+00:00
-- url     : https://prove2.me/theorems/d94d4907-993b-4bc9-a255-0faacfb4b3d0
-- title:
--   §7: transitivity extends the conditional cost formula to every supported state
-- statement:
--   Let $G$ be a compact topological group with continuous unitary representations $V$ on a nonzero finite-dimensional space $K$ and $U$ on a nonzero finite-dimensional output space $B$, both irreducible. Identify $K$ with the range of an isometry $W:K\longrightarrow A\otimes B$. Assume, for every $g\in G$ and every operator $X$ on $K$,
--   $$\operatorname{Tr}_A(WV_gXV_g^\dagger W^\dagger)=U_g\operatorname{Tr}_A(WXW^\dagger)U_g^\dagger.$$
--   Let $T(X)=\operatorname{Tr}_A(WXW^\dagger)$, $P=WW^\dagger$, $\tau=P/\operatorname{Tr}P$, and $m=\min_{\|x\|=1} E(Wx)$, where $E$ is pure-state marginal entropy. An arbitrary ambient environment can be compressed to the finite component span without changing any supported state or entanglement value. The group action need not factor across the two parties.
--
--   Assume $E_c(\tau)=E_f(\tau)$ and that $G$ acts transitively on pure projectors on $K$: for any unit vectors $x,y$ there is $g$ with $|V_gx\rangle\langle V_gx|=|y\rangle\langle y|$. For every density matrix $\rho$ supported on $WK$,
--   $$E_c(\rho)=E_f(\rho)=m.$$
--   The transitivity condition concerns pure states up to global phase and leaves the zero vector outside its domain. It promotes the preceding orbit-mixture conclusion to all supported states.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 12, §7: transitivity extends the conditional cost formula to every supported state

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

/-- PDF p.12: transitivity extends (19) to every supported density matrix. The
projector cost premise is inherited from the preceding paragraph and retained. -/
theorem transitive_cost {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] {a b k : ℕ} (D : CovariantData G a b k)
    (hcost : formationCostBits (projectorState D) = formation (projectorState D)) (htrans : PureTransitive D)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho)
    (hsupport : HasRangeIn (dilationSpace D.W) rho) :
    formationCostBits rho = minimumEntanglement D ∧ formation rho = minimumEntanglement D := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
