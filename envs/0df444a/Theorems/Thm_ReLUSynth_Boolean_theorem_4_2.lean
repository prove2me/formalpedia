-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_theorem_4_2
-- name    : ReLUSynth.Boolean.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:12:13.920574+00:00
-- url     : https://prove2.me/theorems/ede4893b-dc7a-48e3-8af6-e98a0078229d
-- title:
--   Theorem 4.2 — circuit-target exact synthesis is in Σ₂ᴾ and coNP-hard already with W = (0) and n_max = 1
-- statement:
--   For each inventory rule (at-most-once, exactly-once), with an affine output, the language of exact synthesis for a Boolean target supplied by an AND/OR/NOT circuit (instances $(C,W,n_{\max})$ such that some permitted network satisfies $N(x)=C(x)$ for every $x\in\{0,1\}^d$) belongs to $\Sigma_2^P$. Moreover it is coNP-hard: every language in coNP reduces to it by a deterministic polynomial-time many-one reduction whose every image is a well-formed instance with inventory $W=(0)$ and cap $n_{\max}=1$.
--
--   The upper bound is the membership half of the main theorem (Theorem 4.12).
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - encoding: integers in binary, rationals as signed numerator and positive denominator, explicitly listed graphs and lists (p. 9); languages are sets of binary strings (p. 12) → the fixed prefix-free codes encNat (self-delimiting binary), encInt, encRat, encList, Circuit.encode, and a string is in the language only if it is the code of a well-formed yes instance; reason: the paper fixes no concrete code; these are injective with linear overhead, so membership and hardness do not depend on the choice
--   - encoding: Σ₂ᴾ: ∃ a polynomial-length string ∀ a polynomial-length string, polynomial-time predicate; deterministic polynomial-time many-one reductions (pp. 12–13, 16) → the published AvgWorstGap.InSigmaP 2 / IsSigmaPComplete 2 / ComputesFn (certificates of exact length v(|x|), multi-tape NKtLB.Machine); reason: the standard definition; fixed-length certificates are equivalent to bounded ones by padding (the paper's own 'padded as necessary', p. 16)
--   - reading: the lower bound holds with W = (0) and n_max = 1 → the reduction's every image is a well-formed instance whose inventory has the single value 0 and whose cap is 1; reason: the restriction is a property of the produced instances
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 16, Theorem 4.2

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Synthesis

namespace ReLUSynth.Boolean

/-- Theorem 4.2 (p. 16): for each inventory rule, exact synthesis for a Boolean target supplied by
a circuit (affine output) is in `Σ_2^P`, and it is coNP-hard under polynomial-time many-one
reductions whose every image is a well-formed instance with inventory `W = (0)` and cap
`n_max = 1`. -/
theorem theorem_4_2 (rule : InventoryRule) :
    AvgWorstGap.InSigmaP 2 (SynthLang rule) ∧
    ∀ L' : Set (List Bool), InCoNP L' →
      ReducesWithImages L' (SynthLang rule) (fun _ s => ∃ I : SynthInstance,
        s = I.encode ∧ I.WellFormed ∧ I.W.map RatCode.val = [0] ∧ I.nmax = 1) := by sorry

end ReLUSynth.Boolean
