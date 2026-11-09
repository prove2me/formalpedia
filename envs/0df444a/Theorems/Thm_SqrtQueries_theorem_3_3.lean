-- Prove2me | Theorems.Thm_SqrtQueries_theorem_3_3
-- name    : SqrtQueries.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:26.104372+00:00
-- url     : https://prove2.me/theorems/ea3b2cde-39bc-41b0-9a5b-e417cf862305
-- title:
--   Theorem 3.3 — $\Omega(N)$ queries to $U,U^\dagger,cU,cU^\dagger$ but $O(\log N)$ queries to any square root
-- statement:
--   Let $U$ be the oracle of the promise problem of Definition 3.2: $U=U_0=D$ (DIAG) or $U=U_1=e^{iA/4}De^{-iA/4}$ (NOTDIAG), on $\mathbb C^N$.
--
--   1. **Lower bound.** There is a constant $c>0$ such that for every $N\ge1$, every quantum oracle algorithm with query access to $U$, $U^\dagger$ and their controlled versions $cU$, $cU^\dagger$ that decides between DIAG and NOTDIAG with probability at least $2/3$ in both cases makes
--   $$
--   T\ge c\,N
--   $$
--   queries.
--   2. **Upper bound.** There is a constant $C>0$ such that for every $N\ge4$ there is a quantum oracle algorithm making
--   $$
--   T\le C\log N
--   $$
--   queries which, given query access to **any** $V$ with $V^2=U$, decides between DIAG and NOTDIAG with probability at least $2/3$. The algorithm is fixed before the case and the square root $V$ are chosen.
--
--   Thus query access to an arbitrary square root can decrease the query complexity exponentially.
--
--   **Formalization Note** The algorithms are the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each $I_S\oplus(k(O)\otimes I_W)$ with kind $k$ fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map). In clause 1 every query kind is allowed (forward, inverse, conjugate, transpose) with any ancilla sizes; in clause 2 every query is a forward query to $V$. A square root is any complex matrix $V$ with $VV=U$. The labels DIAG and NOTDIAG are `false` and `true`.
--
--   Differences from the source:
--   - generalization: clause 1: algorithms with query access to U, U†, cU, cU† → algorithms whose queries may also be conjugate and transpose queries (and their controlled versions); reason: Remark 3.4 states the lower bound for these as well; algorithms using only forward/inverse queries are a special case
--   - reading: Ω(N) queries → ∃ c > 0 such that c·N ≤ T for every N ≥ 1 and every such algorithm; reason: uniform-constant reading of Ω
--   - reading: O(log N) queries → ∃ C > 0 such that for every N ≥ 4 an algorithm with T ≤ C·log N exists; reason: uniform-constant reading of O; the cutoff is needed since at N = 1 the two oracles coincide and the clause is false, and N ≥ 4 is the range of Proposition 3.7
--   - generalization: clause 2: an algorithm given query access to V → an algorithm all of whose queries are forward (controlled) queries to V; reason: restricting the existential algorithm is stronger; Algorithm 2 uses only such queries
--   - encoding: any V such that V² = U → any complex matrix V with V * V = U_β; reason: U_β has simple spectrum, so every such V is unitary (Fact 2.1); the sets coincide
--   - encoding: quantum oracle algorithm deciding with probability at least 2/3 → the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each I_S\oplus(k(O)\otimes I_W) with kind k fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map); EvaluatesWithBoundedError for clause 1; reason: this is the deferred-measurement normal form of any quantum oracle algorithm: intermediate measurements and adaptive gate choices are deferred with ancillas at no query cost (a query whose kind depends on earlier outcomes is replaced by one controlled query of each kind, at most a factor 4 in T), a mixed input is purified, and the direct sum I_S\oplus O is the controlled query
--   - encoding: DIAG / NOTDIAG → false / true; reason: Boolean labels for the bit b
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Theorem 3.3, p.16

import Mathlib
import Definitions.Def_SqrtQueries_oracle
import Definitions.Def_OracleStateHSP_EvaluatesWithBoundedError

namespace SqrtQueries

/-- **Theorem 3.3** (Exponential separation in black-box setting) of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.16. Let `U` be the oracle
of Definition 3.2 (`U₀ = D` for DIAG, `U₁ = e^{iA/4} D e^{−iA/4}` for NOTDIAG).
1. Any quantum oracle algorithm with query access to `U`, `U†`, `cU` and `cU†` that decides between
   DIAG and NOTDIAG with probability at least `2/3` uses `Ω(N)` queries.
2. There is a quantum oracle algorithm which, given query access to any `V` with `V² = U`, decides
   between DIAG and NOTDIAG with probability at least `2/3` using `O(log N)` queries.

**Formalization Note.** The query model is the published `OracleStateHSP.QueryAlgorithm`: `T`
queries, each `I_S ⊕ (k(O) ⊗ I_W)` with a kind `k` fixed in advance, interleaved with
oracle-independent unitaries, from a unit initial state, then a computational-basis measurement
with an output map (`false` = DIAG, `true` = NOTDIAG). The direct sum gives the controlled
queries. Clause 1 allows every kind (forward, inverse, conjugate, transpose; Remark 3.4) and any
ancilla sizes `a`, `b`; `Ω(N)` is one constant `c > 0` with `c N ≤ T` for all `N ≥ 1`. Clause 2
uses forward queries only; `O(log N)` is one constant `C` for all `N ≥ 4` (at `N = 1` the two
oracles coincide), and the algorithm is chosen before the bit `β` and the square root `V`, which
is any complex matrix with `V * V = U_β`. -/
theorem theorem_3_3 :
    (∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (T a b : ℕ)
        (A : OracleStateHSP.QueryAlgorithm (Fin N) (Fin a) (Fin b) T)
        (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (Fin N × Fin b))) (out : Fin a ⊕ (Fin N × Fin b) → Bool),
        OracleStateHSP.EvaluatesWithBoundedError A ψ₀ out (oracle N) id → c * N ≤ T) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], 4 ≤ N →
      ∃ (T a b : ℕ) (A : OracleStateHSP.QueryAlgorithm (Fin N) (Fin a) (Fin b) T)
        (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (Fin N × Fin b))) (out : Fin a ⊕ (Fin N × Fin b) → Bool),
        (∀ i, A.kind i = OracleStateHSP.QueryKind.fwd) ∧ (T : ℝ) ≤ C * Real.log N ∧ ‖ψ₀‖ = 1 ∧
        ∀ (β : Bool) (V : Matrix (Fin N) (Fin N) ℂ), V * V = oracle N β →
          (2 / 3 : ℝ) ≤ A.outputProb V ψ₀ out β) := by sorry

end SqrtQueries
