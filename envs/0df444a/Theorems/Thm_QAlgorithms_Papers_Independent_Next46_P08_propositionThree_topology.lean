-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_propositionThree_topology
-- name    : QAlgorithms.Papers.Independent.Next46.P08.propositionThree_topology
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:52:07.52907+00:00
-- url     : https://prove2.me/theorems/a8bcbc0a-7125-402e-bfb6-df464539fd1b
-- title:
--   Proposition 3 A–B: general-input ECD convergence and strong topology
-- statement:
--   Let $A,B$ be infinite-dimensional separable complex Hilbert systems, and let $H_A$ be any positive densely defined self-adjoint Hamiltonian, possibly with continuous spectrum. Its extended energy is the spectral-cutoff supremum and $E_0^A$ is its spectrum infimum. Fix $E>E_0^A$. Define $D_E(\Phi,\Psi)$ as the supremum of $\|((\Phi-\Psi)\otimes\mathrm{Id}_R)(\omega)\|_1$ over all normalized states on $A\otimes R$ with input marginal energy at most $E$, for a fixed infinite-dimensional separable reference $R$.
--
--   For every channel sequence $(\Phi_n)$ and channel $\Phi_0$,
--
--   $$
--   D_E(\Phi_n,\Phi_0)\longrightarrow0\quad\Longrightarrow\quad
--   \|\Phi_n(\rho)-\Phi_0(\rho)\|_1\longrightarrow0\quad\text{for every input state }\rho.
--   $$
--
--   If $H_A$ additionally has a complete countably infinite eigenbasis with eigenvalues of finite multiplicity tending to infinity, the implication is an equivalence and the topology induced by $D_E$ equals the strong channel topology.
--
--   This separates the unconditional direction from the direction requiring spectral compactness. Neither direction assumes a Gibbs condition. The formalization reuses the accepted closed quadratic form and its expectation, equivalent to the actual self-adjoint observable and spectral-cutoff energy.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 6, Abstract topology result, precisely Proposition 3 A–B

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Proposition 3 A–B and footnote 3, PDF pp.6–8. A has arbitrary positive
densely defined H on infinite-dimensional separable input and output systems,
as stipulated in Section 2, with no discrete/Gibbs premise. B adds the full discrete
finite-multiplicity spectral condition and gives both the converse for
sequences and equality with the actual strong topology. -/
theorem propositionThree_topology {I J : Type} [Countable I] [Nonempty I] [Infinite I]
    [Countable J] [Nonempty J] [Infinite J] (H : Forms.PositiveObservable I)
    (E : ℝ) (hE : formGroundEnergy H < E) :
    (∀ (seq : ℕ → QAlgorithms.Papers.Independent.Claimed50.P32.StrongChannel I J)
        (Phi : QAlgorithms.Papers.Independent.Claimed50.P32.StrongChannel I J),
      Tendsto (fun n => formEcdMagnitude H E (seq n) Phi) atTop (nhds 0) →
        StrongConvergence seq Phi) ∧
    (DiscreteSpectrum H →
      formEcdTopology H E =
        (inferInstance : TopologicalSpace
          (QAlgorithms.Papers.Independent.Claimed50.P32.StrongChannel I J)) ∧
      ∀ (seq : ℕ → QAlgorithms.Papers.Independent.Claimed50.P32.StrongChannel I J)
        (Phi : QAlgorithms.Papers.Independent.Claimed50.P32.StrongChannel I J),
        Tendsto (fun n => formEcdMagnitude H E (seq n) Phi) atTop (nhds 0) ↔
          StrongConvergence seq Phi) := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
