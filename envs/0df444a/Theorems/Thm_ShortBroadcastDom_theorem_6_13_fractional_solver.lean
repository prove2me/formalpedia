-- Prove2me | Theorems.Thm_ShortBroadcastDom_theorem_6_13_fractional_solver
-- name    : ShortBroadcastDom.theorem_6_13_fractional_solver
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:22.561642+00:00
-- url     : https://prove2.me/theorems/5f17b8fc-3425-43e1-ab5f-d9e35ba7287f
-- title:
--   Theorem 6.13 — a constant-round $(1+\delta)$-approximate fractional covering solver on $\mathcal C_a$
-- statement:
--   For every fixed rational $a\ge1$, integer $B_0\ge1$ and rational $\delta>0$ there is a deterministic broadcast CONGEST algorithm with a round count $T$ and a common denominator $Q\ge1$ depending only on $a,B_0,\delta$, with the following guarantee. On every finite graph $G\in\mathcal C_a$ with demands $R$ and integer costs $1\le c_v\le B_0$ (known locally), it computes a vector $x\in[0,1]^{V(G)}$ with $Qx_v\in\mathbb Z$ such that
--
--   $$
--   \sum_{v\in N_G[r]}x_v\ge1\ (r\in R)\qquad\text{and}\qquad\sum_vc_vx_v\le(1+\delta)\,\tau_{R,c}(G).
--   $$
--
--   The algorithm uses messages of $O(\log(n+1))$ bits and needs no embedding, orientation, decomposition, initial solution, graph order or degree bound. It is the fractional solver run in the proof of Theorem C.
--
--   **Formalization Note** The local input is (demand bit, integer cost) and the output a rational; the identifier exponent $k$ only affects the message constant.
--
--   Differences from the source:
--   - reading: broadcast CONGEST with O(log(n+1))-bit identifiers and messages → multiset reception; ∃ algorithm ∃ T ∃ Q, ∀ k ∃ c, identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: less information for the algorithm, and the algorithm is independent of the identifier constant: at least as strong as the paper
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §6.5, p.37 (PDF p.40), Theorem 6.13

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_BroadcastAlg

namespace ShortBroadcastDom

/-- **Theorem 6.13 (the fractional solver, closed neighbourhoods).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §6.5, p.37 (PDF 40):
"For every fixed rational a ≥ 1, integer B0 ≥ 1, and rational δ > 0, there is a deterministic
broadcast CONGEST algorithm with the following guarantee. On a graph G ∈ Ca, with demands R and
integer costs 1 ≤ cv ≤ B0, it computes a feasible vector x ∈ [0, 1]^V(G) such that
∑_v cvxv ≤ (1 + δ)τR,c(G). The number of rounds and a common denominator for all output coordinates
depend only on a, B0, δ. The algorithm requires no embedding, orientation, decomposition, initial
solution, graph order, or maximum-degree bound."

**Formalization Note** The local input is `(demand bit, integer cost)`, the output a rational
`x_v`; the algorithm, the round count `T` and the common denominator `Q ≥ 1` are fixed before the
graph; the identifier exponent `k` only affects the message constant. -/
theorem theorem_6_13_fractional_solver (a : ℚ) (ha : 1 ≤ a) (B0 : ℕ) (hB0 : 1 ≤ B0) (δ : ℚ) (hδ : 0 < δ) :
    ∃ alg : BroadcastAlg (Bool × ℕ) ℚ, ∃ T Q : ℕ, 0 < Q ∧ ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ) (inp : V → Bool × ℕ),
        ValidIds k (Fintype.card V) id → InClassC (a : ℝ) G →
        (∀ v, 1 ≤ (inp v).2 ∧ (inp v).2 ≤ B0) →
          MsgBounded alg G id inp T c (Fintype.card V) ∧
          (∀ v, 0 ≤ alg.realOut G id inp T v ∧ alg.realOut G id inp T v ≤ 1) ∧
          (∀ v, ∃ z : ℤ, (Q : ℚ) * alg.output G id inp T v = z) ∧
          (∀ r ∈ demandsOf inp, 1 ≤ ∑ v ∈ closedNbhd G r, alg.realOut G id inp T v) ∧
          ∑ v, costsOf inp v * alg.realOut G id inp T v ≤
            (1 + (δ : ℝ)) * tau G (demandsOf inp) (costsOf inp) := by sorry

end ShortBroadcastDom
