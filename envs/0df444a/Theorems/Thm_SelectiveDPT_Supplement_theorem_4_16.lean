-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_4_16
-- name    : SelectiveDPT.Supplement.theorem_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:35:31.167858+00:00
-- url     : https://prove2.me/theorems/4795b8d8-923a-479f-9ff5-7d52e1483557
-- title:
--   Theorem 4.16 (corrected: $n\ge2$) — general quantum time-space tradeoff $T \ge Cn^{2.5}/S$ for matrix mapping
-- statement:
--   There is a constant $C > 0$ such that for every $n \ge 2$ and every $A \in \mathbb Z^{n \times n}$ with pairwise distinct entries the following holds. Every algorithm of the general quantum query model with space $S < n/16$ and $T$ layers (queries) that computes the matrix mapping $g_A(F,\tilde F) = FA\tilde F^{\mathsf T}$ with success probability at least $2^{-S}$ satisfies
--   $$C\, n^{5/2} \le S\, T, \qquad\text{i.e.}\quad T \ge \frac{C\, n^{2.5}}{S}.$$
--
--   The algorithm may make intermediate measurements and write output pairs $((i,j), v)$ at input-dependent times; it computes $g_A$ when every written value is correct and every entry is written. The success probability is averaged over uniformly random function matrices $F, \tilde F$. Grover search gives a matching upper bound up to logarithmic factors (Proposition 4.15).
--
--   Differences from the source:
--   - correction: any A ∈ Z^{n×n} (every n) → n ≥ 2; reason: at n = 1, S < 1/16 forces S = 0 and the claim T ≥ C/0 = ∞ is false: a one-layer algorithm writes ((1,1), A₁₁) with certainty, using no passed qubits
--   - generalization: the general quantum query model of §2.3 (S qubits passed between layers; each layer: oracle O, fresh ancillas in |0⟩, a unitary U_t, a flag measurement and, on flag 1, measuring and discarding an output register read as an output pair; start in |0⟩) → SpaceBoundedAlg: a passed register with |P| ≤ 2^S basis states whose basis is labelled by queries, any input-independent start state, and in each layer the oracle followed by any finite Kraus instrument with outcome-dependent outputs; reason: every §2.3 algorithm is an instance (the measurement after U_t with discarding is a Kraus instrument; S qubits have 2^S basis states); the lower bound for the larger class implies the source's
--   - reading: computing g_A(F, F̃) → every written pair ((i, j), v) has v = g_A(F, F̃)_{ij} and every (i, j) ∈ [n]² is written (ComputesMatMap); reason: an algorithm computing a function writes the correct value of every output coordinate and no wrong one
--   - reading: success probability at least 2^{−S} → success probability averaged over uniform function matrices F, F̃ at least 2^{−S} (matMapSuccess); reason: the proof works with uniformly random F, F̃ (Lemma 4.18); the average is at least the worst case, so this is the stronger reading
--   - encoding: T ≥ Cn^{2.5}/S → C·n^{5/2} ≤ S·T; reason: equivalent for S > 0, and for S = 0 it says that no algorithm exists, which avoids Lean's x/0 = 0
--   - encoding: A with unique entries; input the pair (F, F̃) of function matrices → (i, j) ↦ A_{ij} injective; the 2n² bits of (F, F̃) indexed by Fin 2 × Fin n × Fin n, F given by f : Fin n → Fin n; reason: a function matrix is exactly the matrix of a function [n] → [n] (Definition 4.13)
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 4.16, p.39; §2.3, p.11; Definitions 4.13–4.14, p.37

import Mathlib
import Definitions.Def_SelectiveDPT_Supplement_SpaceBoundedAlg
import Definitions.Def_SelectiveDPT_Supplement_matMap

namespace SelectiveDPT.Supplement

/-- Theorem 4.16 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.39: there exists `C > 0` such
that for any `A ∈ ℤ^{n×n}` with unique entries the following holds. Any quantum query algorithm
computing `g_A(F, F̃)` with space `S < n/16` and success probability at least `2^{−S}` requires
`T ≥ C n^{2.5}/S` quantum queries.

**Formalization Note.** The algorithm is any `T`-layer algorithm of §2.3's general quantum query
model (`SpaceBoundedAlg`: intermediate measurements, a write-only output tape of pairs
`((i, j), v)`, input-dependent output order) on the `2n²` input bits of `(F, F̃)`, whose passed
register has at most `2^S` basis states. "Computes `g_A`" means every written pair is correct and
every coordinate is written (`ComputesMatMap`); the success probability is averaged over uniform
`F, F̃ ∼ F_n` (`matMapSuccess`, as in Lemma 4.18), which bounds the worst case too. "Unique
entries" is injectivity of `(i, j) ↦ A_{ij}`. `C` is chosen before `n`, `A`, `S`, `T` and the
algorithm; the conclusion is `C n^{5/2} ≤ S · T` (for `S = 0` it says that no algorithm exists).
**Correction:** `n ≥ 2` (at `n = 1`, `S < 1/16` forces `S = 0`, and a one-layer algorithm writes
`((1,1), A₁₁)` with certainty). -/
theorem theorem_4_16 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (A : Matrix (Fin n) (Fin n) ℤ),
      Function.Injective (fun p : Fin n × Fin n => A p.1 p.2) →
      ∀ (S T : ℕ), (S : ℝ) < n / 16 →
      ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P ≤ 2 ^ S →
      ∀ alg : SpaceBoundedAlg (Fin 2 × Fin n × Fin n) P ((Fin n × Fin n) × ℤ) 2 T,
        (2 : ℝ) ^ (-(S : ℝ)) ≤ matMapSuccess A alg →
        C * (n : ℝ) ^ ((5 : ℝ) / 2) ≤ (S : ℝ) * T := by sorry

end SelectiveDPT.Supplement
