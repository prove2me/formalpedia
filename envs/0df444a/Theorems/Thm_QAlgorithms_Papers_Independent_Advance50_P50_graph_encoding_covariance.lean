-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_graph_encoding_covariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.graph_encoding_covariance
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:21:25.516773+00:00
-- url     : https://prove2.me/theorems/a52c035a-3224-4702-91c7-accd55405584
-- title:
--   Eqs.(40)–(42): covariance of graph-state encoding
-- statement:
--   Let $G,H$ be simple graphs on the same $n$ vertices and $p$ a vertex permutation satisfying $\{p(i),p(j)\}\in E(H)$ exactly when $\{i,j\}\in E(G)$. Let $P$ be its physical site permutation, $t>0$, and $\rho_{\rm in}$ a permutation-invariant density matrix. Put $H_G=\sum_{\{i,j\}\in E(G)}Z_iZ_j+\sum_iX_i$, with unordered edges counted once, $W_G=e^{-itH_G}$, and $\rho_G=W_G\rho_{\rm in}W_G^\dagger$. Then
--
--   $$H_H=PH_GP^\dagger,\qquad W_H=PW_GP^\dagger,\qquad \rho_H=P\rho_GP^\dagger.$$
--
--   The encoding therefore respects vertex relabelling and isomorphism-class labels. No injective graph encoding or distinguishing evolution time is claimed.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 14, Eqs.(40)–(42): covariance of graph-state encoding

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.14–15, Eqs.(40)–(42): encoding is covariant under a vertex
bijection preserving adjacency. Printed P rho P is corrected to P rho P†;
general permutations are not self-adjoint. No injectivity is claimed.
Printed: PDF pp.14-15 defines graph isomorphism by an edge bijection and repeatedly writes P rho P and P H P for arbitrary permutations P.
Changed: Require a vertex permutation preserving adjacency and use P rho P-dagger, P H P-dagger and P exp(-itH) P-dagger throughout.
Why: An arbitrary edge bijection only fixes edge counts. The Ising-encoding proof relabels vertices and conjugates physical operators. A three-cycle has P-dagger different from P, so the adjoint is indispensable. No separating observable or injective encoding is added. -/
theorem graph_encoding_covariance {n : ℕ} (G H : SimpleGraph (Fin n))
    (p : Equiv.Perm (Fin n)) (hiso : ∀ i j, H.Adj (p i) (p j) ↔ G.Adj i j)
    (t : ℝ) (ht : 0 < t) (rho : Mat (Qubits n)) (hrho : IsDensityMatrix rho)
    (hfixed : ∀ q : Equiv.Perm (Fin n), conjSuperop (sitePermutation q) rho = rho) :
    graphHamiltonian H = conjSuperop (sitePermutation p) (graphHamiltonian G) ∧
    graphEvolution H t = conjSuperop (sitePermutation p) (graphEvolution G t) ∧
    graphEncoding H t rho = conjSuperop (sitePermutation p) (graphEncoding G t rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
