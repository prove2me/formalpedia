-- Prove2me | Theorems.Thm_SqrtQueries_proposition_3_7
-- name    : SqrtQueries.proposition_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:24.839731+00:00
-- url     : https://prove2.me/theorems/81a8432b-afa3-430b-81dc-e6ab5a82027e
-- title:
--   Proposition 3.7 — an $O(\log N)$-query algorithm outputs DIAG on roots of $U_0$, NOTDIAG w.p. $\ge0.9$ on roots of $U_1$
-- statement:
--   There is a constant $C>0$ such that for every $N\ge4$ there is a quantum oracle algorithm, querying an unknown oracle $V$ at most $C\log N$ times, which
--
--   1. outputs DIAG with probability $1$ for every square root $V$ of $U_0$, and
--   2. outputs NOTDIAG with probability at least $0.9$ for every square root $V$ of $U_1$,
--
--   where $U_0$, $U_1$ are the oracles of Definition 3.2. The algorithm is fixed before the oracle is chosen.
--
--   This is the upper bound of the separation: query access to any square root makes the problem solvable with $O(\log N)$ queries.
--
--   **Formalization Note** The algorithm is the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each $I_S\oplus(k(O)\otimes I_W)$ with kind $k$ fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map) with all queries forward; its output map is into $\{\text{DIAG},\text{NOTDIAG}\}=\{\mathtt{false},\mathtt{true}\}$. A square root is any complex matrix $V$ with $VV=U_b$.
--
--   Differences from the source:
--   - reading: queries the oracle O(log N) times → ∃ C > 0 such that for every N ≥ 4 the algorithm makes T ≤ C·log N queries; reason: uniform constant reading of O; N ≥ 4 is the proposition's range
--   - reading: outputs DIAG for any square root of U₀ → outputs false with probability 1; reason: the proof of Theorem 3.9 shows the algorithm never errs in the DIAG case, and the contrast with 'probability ≥ 0.9' in the NOTDIAG case
--   - generalization: an algorithm that queries the oracle → an algorithm all of whose queries are forward queries to V (controlled through the direct sum); reason: restricting the existential algorithm to forward queries is stronger; Algorithm 2 uses only such queries
--   - encoding: quantum oracle algorithm → the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each I_S\oplus(k(O)\otimes I_W) with kind k fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map); reason: this is the deferred-measurement normal form of any quantum oracle algorithm: intermediate measurements and adaptivity are deferred with ancillas at no query cost, a mixed input is purified, and the direct sum I_S\oplus O is the controlled query
--   - encoding: DIAG / NOTDIAG → false / true; reason: Boolean labels for the bit b
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Proposition 3.7, p.17

import Mathlib
import Definitions.Def_SqrtQueries_oracle
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb

namespace SqrtQueries

/-- **Proposition 3.7** (Distinguishing is efficient with roots) of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.17: for `N ≥ 4` there is an
algorithm which, given an unknown oracle, outputs DIAG for any square root of `U₀`, while it
outputs NOTDIAG with probability `≥ 0.9` for any square root of `U₁`; it queries the oracle
`O(log N)` times.

**Formalization Note.** `O(log N)` is one constant `C` for all `N ≥ 4`. The algorithm (queries,
ancillas, gates, unit initial state `ψ₀`, output map into `Bool`, `false` = DIAG, `true` =
NOTDIAG) is chosen before the oracle `V`, and all its queries are forward queries to `V` (applied
as controlled `V` through the direct sum of the published `OracleStateHSP.QueryAlgorithm`).
"Outputs DIAG" is output `false` with probability `1` (Theorem 3.9's proof: "it never errs in the
DIAG case"). A square root of `U_b` is any complex matrix `V` with `V * V = U_b`. -/
theorem proposition_3_7 : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], 4 ≤ N →
    ∃ (T a b : ℕ) (A : OracleStateHSP.QueryAlgorithm (Fin N) (Fin a) (Fin b) T)
      (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (Fin N × Fin b))) (out : Fin a ⊕ (Fin N × Fin b) → Bool),
      ‖ψ₀‖ = 1 ∧ (∀ i, A.kind i = OracleStateHSP.QueryKind.fwd) ∧ (T : ℝ) ≤ C * Real.log N ∧
      (∀ V : Matrix (Fin N) (Fin N) ℂ, V * V = oracle N false →
        A.outputProb V ψ₀ out false = 1) ∧
      (∀ V : Matrix (Fin N) (Fin N) ℂ, V * V = oracle N true →
        (9 / 10 : ℝ) ≤ A.outputProb V ψ₀ out true) := by sorry

end SqrtQueries
