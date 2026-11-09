-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_uniform_edge_listing
-- name    : SubsetSumPartialMatch.SubsetSum.uniform_edge_listing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:36.940572+00:00
-- url     : https://prove2.me/theorems/48336745-2554-4646-bea2-e082b4c8e520
-- title:
--   Corollary 3.2 — uniform edge-listing algorithms
-- statement:
--   Let $(l,r)\in K(1/2)$ and $\varepsilon>0$. There are EXACT$_\mathbb Z$ circuits $C_n$ computing $P_{n,1/2}$, one for each even $n\ge2$, and deterministic algorithms $A_L$ and $A_R$ with the following properties.
--
--   1. Given $x\in\{0,1\}^n$, the algorithm $A_L$ lists all edges $x\to e$ of $C_n$, each as a middle-gate name $e$ with its coefficient, in time $O(2^{(l+\varepsilon)n})$.
--   2. Given $y\in\{0,1,*\}^n$ with $|S(y)|=n/2$, the algorithm $A_R$ lists all edges $e\to y$ of $C_n$, each as a middle-gate name $e$ with its coefficient, in time $O(2^{(r+\varepsilon)n})$.
--
--   The mere existence of good circuits would only give a nonuniform algorithm; this corollary makes them explicit.
--
--   Differences from the source:
--   - encoding: middle-gate names → an injective map from the middle gates to $\mathbb Z$, part of the conclusion; reason: a name must be a machine word; the time bound charges its length
--   - encoding: $O(\cdot)$ → one constant $c>0$ valid for all even $n\ge2$; reason: finitely many small $n$ are absorbed in the constant
--   - encoding: input $x$ or $y$ → the word $n$ followed by the string, one word per position; output is name, coefficient, name, coefficient, …; reason: machine presentation of the same data
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 17, Corollary 3.2

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum

/-- Corollary 3.2. For `(l, r) ∈ K(1/2)` and `ε > 0` there are EXACT_Z circuits `C_n` for
`P_{n,1/2}`, one for each even `n ≥ 2`, with injective integer names for their middle gates, and
deterministic programs `A_L`, `A_R` such that `A_L` lists all edges `x → e` of `C_n`, each as a name
with its coefficient, in time `O(2^{(l+ε)n})`, and `A_R` lists all edges `e → y` in time
`O(2^{(r+ε)n})`. -/
theorem uniform_edge_listing {l r ε : ℝ} (hK : (l, r) ∈ K (1 / 2)) (hε : 0 < ε) :
    ∃ (C : ∀ n : ℕ, LinCircuit (BinStr n) (PMCol n (1 / 2)))
      (name : ∀ n : ℕ, (C n).Mid → ℤ) (AL AR : Program) (c : ℝ),
      Deterministic AL ∧ Deterministic AR ∧ 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → Even n →
        (C n).Computes (pm n (1 / 2)) ∧ Function.Injective (name n) ∧
        (∀ x : BinStr n, ∃ es : List (C n).Mid,
          Enumerates es {e | (C n).L x e ≠ 0} ∧
          Outputs AL blankTape ((n : ℤ) :: binWords x)
            (edgeWords (name n) (fun e => (C n).L x e) es) ∧
          CostWithin AL blankTape ((n : ℤ) :: binWords x) (c * (2 : ℝ) ^ ((l + ε) * n))) ∧
        (∀ y : PMCol n (1 / 2), ∃ es : List (C n).Mid,
          Enumerates es {e | (C n).R e y ≠ 0} ∧
          Outputs AR blankTape ((n : ℤ) :: queryWords y.1)
            (edgeWords (name n) (fun e => (C n).R e y) es) ∧
          CostWithin AR blankTape ((n : ℤ) :: queryWords y.1)
            (c * (2 : ℝ) ^ ((r + ε) * n))) := by sorry

end SubsetSumPartialMatch.SubsetSum
