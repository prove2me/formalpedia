-- Prove2me | Theorems.Thm_SqrtQueries_hybrid_bound
-- name    : SqrtQueries.hybrid_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:18.446209+00:00
-- url     : https://prove2.me/theorems/b91155d3-cae9-4e98-b01b-6fe783eeb10e
-- title:
--   Proof of Theorem 3.3, hybrid bound — end states $T\pi/(2N)$ apart
-- statement:
--   Let $N\ge1$ and let $\mathcal A$ be any $T$-query algorithm on a space $\mathbb C^S\oplus(\mathbb C^N\otimes\mathbb C^W)$: oracle-independent unitaries $V_0,\dots,V_T$ and, between them, $T$ queries, each of which applies $I_S\oplus(k(O)\otimes I_W)$ for a fixed kind $k(O)\in\{O,O^\dagger,\overline O,O^{\mathsf T}\}$ (so controlled queries are included). For every unit vector $\psi_0$, the final states on the two oracles of Definition 3.2 satisfy
--   $$
--   \big\|\mathcal A^{U_0}\psi_0-\mathcal A^{U_1}\psi_0\big\|\le T\cdot\frac{\pi}{2N}.
--   $$
--
--   This is the hybrid argument of the lower bound: the end states under DIAG and NOTDIAG are $O(T/N)$ apart in $L^2$ distance for a pure input.
--
--   **Formalization Note** The algorithm is the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each $I_S\oplus(k(O)\otimes I_W)$ with kind $k$ fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map). The norm is the Euclidean norm.
--
--   Differences from the source:
--   - generalization: end states O(T/N) apart in L2 distance → ‖A^{U₀}ψ₀ − A^{U₁}ψ₀‖ ≤ T·π/(2N); reason: the explicit constant π/(2N) is that of Proposition 3.5; the bound implies the printed O(T/N)
--   - generalization: queries to U, U†, cU, cU† → every query kind (forward, inverse, conjugate, transpose), each controlled through the direct sum; reason: the bound holds for all kinds (Remark 3.4) and specializes to the paper's forward/inverse queries
--   - encoding: any T-query algorithm with pure input → the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each I_S\oplus(k(O)\otimes I_W) with kind k fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map); reason: the paper's hybrid argument concerns this circuit form; this is the deferred-measurement normal form of any quantum oracle algorithm: intermediate measurements and adaptive gate choices are deferred with ancillas at no query cost (a query whose kind depends on earlier outcomes is replaced by one controlled query of each kind, at most a factor 4 in T), a mixed input is purified, and the direct sum I_S\oplus O is the controlled query
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), proof of Theorem 3.3, hybrid argument, p.18

import Mathlib
import Definitions.Def_SqrtQueries_oracle
import Definitions.Def_OracleStateHSP_QueryAlgorithm

namespace SqrtQueries

/-- **Hybrid bound** in the proof of Theorem 3.3 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.18: "the end states of any `T`-query
algorithm under the two cases DIAG and NOTDIAG are `O(T/N)` apart in `L2` distance, assuming the
input is pure". Explicitly: for every `N ≥ 1`, every `T`-query algorithm `A` (any query kinds,
controlled through the direct sum) and every unit initial state `ψ₀`,
`‖A^{U₀} ψ₀ − A^{U₁} ψ₀‖ ≤ T · π/(2N)`.

**Formalization Note.** The query model is the published `OracleStateHSP.QueryAlgorithm` on
`S ⊕ (ℂ^N ⊗ W)` (forward, inverse, conjugate and transpose queries, each applied as
`I_S ⊕ (k(O) ⊗ I_W)`, so controlled queries are included). The constant `π/(2N)` is the bound of
Proposition 3.5; the page's `O(T/N)` is stated with this explicit constant. The norm is the
Euclidean norm of `EuclideanSpace`. -/
theorem hybrid_bound (N : ℕ) [NeZero N] {S W : Type*} [Fintype S] [Fintype W] [DecidableEq S]
    [DecidableEq W] {T : ℕ} (A : OracleStateHSP.QueryAlgorithm (Fin N) S W T)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Fin N × W))) (hψ₀ : ‖ψ₀‖ = 1) :
    ‖A.finalState (oracle N false) ψ₀ - A.finalState (oracle N true) ψ₀‖ ≤
      T * (Real.pi / (2 * N)) := by sorry

end SqrtQueries
