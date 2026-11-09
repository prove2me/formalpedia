-- Prove2me | Theorems.Thm_SqrtQueries_notdiag_search
-- name    : SqrtQueries.notdiag_search
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:31:41.588208+00:00
-- url     : https://prove2.me/theorems/58f8b5ae-b8a3-4300-884c-289d221ebcf7
-- title:
--   Proof of Theorem 3.9 — finding the discontinuity $j^*$ with $O(\log N)$ queries to any root of $U_1$
-- statement:
--   There is a constant $C>0$ such that for every $N\ge2$ there is a quantum oracle algorithm making at most $C\log N$ forward (controlled) queries to an oracle $V$ which, for **every** square root $V$ of $U_1=e^{iA/4}De^{-iA/4}$, outputs with probability $1$ an index $j^*$ with
--   $$
--   r_{j^*+1}=-\omega_{2N}\,r_{j^*},
--   $$
--   where $r_j$ is the eigenvalue of $V$ at $e^{iA/4}|j\rangle$. The algorithm (its queries, gates, initial state and output map) does not depend on $V$; the preparation $\tilde U|j\rangle|0\rangle=|j\rangle e^{iA/4}|j\rangle$ is one of its fixed gates.
--
--   This is the first step of Algorithm 2 in the NOTDIAG case: because $\tilde U$ prepares the exact eigenvectors of $V$, the zero-error binary search of Lemma 3.1 finds the discontinuity.
--
--   **Formalization Note** The algorithm is the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each $I_S\oplus(k(O)\otimes I_W)$ with kind $k$ fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map) with all queries forward. The success probability is the total output probability of the indices satisfying the relation; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: we get the j* with the guarantees of Lemma 3.1 (exact case: O(log N) queries, success probability 1) → ∃ C > 0, ∀ N ≥ 2, an algorithm with T ≤ C·log N forward queries outputting such a j* with probability 1, for every square root V of U₁; reason: Ũ prepares the true eigenvectors of V and V is queried exactly, which is the zero-error clause of Lemma 3.1; O(log N) is a uniform constant, and N ≥ 2 makes log N positive
--   - encoding: quantum oracle algorithm with oracle access to V → the published query model `OracleStateHSP.QueryAlgorithm` (T queries, each I_S\oplus(k(O)\otimes I_W) with kind k fixed in advance, interleaved with oracle-independent unitaries, from a unit initial state, then a computational-basis measurement with an output map); reason: this is the deferred-measurement normal form of any quantum oracle algorithm: intermediate measurements and adaptivity are deferred with ancillas at no query cost, a mixed input is purified, and the direct sum I_S\oplus O is the controlled query
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), proof of Theorem 3.9, p.20 (with the exact clause of Lemma 3.1, p.14)

import Mathlib
import Definitions.Def_SqrtQueries_oracle
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb

namespace SqrtQueries

open Matrix

open Classical in
/-- **NOTDIAG search** in the proof of Theorem 3.9 of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript (sha256 783868e7…c5f15a), p.20 (with the exact clause of Lemma 3.1,
p.14). There is a constant `C` such that for every `N ≥ 2` some algorithm making at most
`C log N` forward queries to an oracle `V`, with `Ũ|j⟩|0⟩ = |j⟩ e^{iA/4}|j⟩` as a fixed gate,
outputs, for **every** square root `V` of `U₁`, with probability `1` an index `j*` with
`r_{j*+1} = −ω_{2N} r_{j*}`, where `r_j` is the eigenvalue of `V` at `e^{iA/4}|j⟩`.

**Formalization Note.** The algorithm (number of queries `T`, ancilla sizes, gates, initial unit
state `ψ₀` and output map) is chosen before `V`. The query model is the published
`OracleStateHSP.QueryAlgorithm`; every query is forward (`kind = fwd`), applied as
`I ⊕ (V ⊗ I)` (controlled `V`). Fixed oracle-independent gates such as `Ũ` are among the
algorithm's unitaries. The success probability is the sum of the output probabilities of all
indices satisfying the discontinuity relation; `Real.log` is the natural logarithm. The range
`N ≥ 2` makes `log N > 0`. -/
theorem notdiag_search : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N], 2 ≤ N →
    ∃ (T a b : ℕ) (A : OracleStateHSP.QueryAlgorithm (Fin N) (Fin a) (Fin b) T)
      (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (Fin N × Fin b))) (out : Fin a ⊕ (Fin N × Fin b) → Fin N),
      ‖ψ₀‖ = 1 ∧ (∀ i, A.kind i = OracleStateHSP.QueryKind.fwd) ∧ (T : ℝ) ≤ C * Real.log N ∧
      ∀ (V : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ), V * V = oracle N true →
        (∀ j, V *ᵥ (NormedSpace.exp ((Complex.I / 4) • smearA N) *ᵥ Pi.single j 1) =
          r j • (NormedSpace.exp ((Complex.I / 4) • smearA N) *ᵥ Pi.single j 1)) →
        ∑ j ∈ Finset.univ.filter (fun j => r (j + 1) = -MagnonCode.AQEDC.omega (2 * N) * r j),
          A.outputProb V ψ₀ out j = 1 := by sorry

end SqrtQueries
