-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_theorem_4_12
-- name    : ReLUSynth.Boolean.theorem_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:12:03.375253+00:00
-- url     : https://prove2.me/theorems/51dae54c-bf0a-4a06-89cf-f7409a94d26e
-- title:
--   Theorem 4.12 — exact synthesis of a circuit-specified Boolean target is Σ₂ᴾ-complete under either rule, hard already with four neurons and a positive threshold target
-- statement:
--   Under either the at-most-once or the exactly-once inventory rule, with an affine output, the language of exact synthesis for a Boolean target supplied by an AND/OR/NOT circuit — codes of instances $(C,W,n_{\max})$ such that some permitted ReLU network built from the occurrences of $W$ with at most $n_{\max}$ computational vertices satisfies
--   $$N(x)=C(x)\qquad\text{for every }x\in\{0,1\}^d$$
--   — is $\Sigma_2^P$-complete under deterministic polynomial-time many-one reductions. Moreover, every $\Sigma_2^P$ language reduces to it by such a reduction whose every image is a well-formed instance with cap $n_{\max}=4$ (including the output) and a circuit computing a threshold function $x\mapsto[\sum_tc_tx_t\ge\theta]$ with all $c_t>0$ rational (hence monotone).
--
--   This is the paper's headline result (Theorem 1.1): exact synthesis from a parameter multiset is $\Sigma_2^P$-complete already with four neurons.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - encoding: integers in binary, rationals as signed numerator and positive denominator, explicitly listed graphs and lists (p. 9); languages are sets of binary strings (p. 12) → the fixed prefix-free codes encNat (self-delimiting binary), encInt, encRat, encList, Circuit.encode, and a string is in the language only if it is the code of a well-formed yes instance; reason: the paper fixes no concrete code; these are injective with linear overhead, so membership and hardness do not depend on the choice
--   - encoding: Σ₂ᴾ: ∃ a polynomial-length string ∀ a polynomial-length string, polynomial-time predicate; deterministic polynomial-time many-one reductions (pp. 12–13, 16) → the published AvgWorstGap.InSigmaP 2 / IsSigmaPComplete 2 / ComputesFn (certificates of exact length v(|x|), multi-tape NKtLB.Machine); reason: the standard definition; fixed-length certificates are equivalent to bounded ones by padding (the paper's own 'padded as necessary', p. 16)
--   - reading: hardness holds with a computational-node budget of four, even when the circuit computes a monotone threshold with positive rational coefficients → every Σ₂ᴾ language reduces through a reduction whose every image is a well-formed instance with nmax = 4 and Circuit.IsPosThreshold; reason: the restrictions are properties of the produced instances; positive coefficients make the threshold monotone
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 27, Theorem 4.12 (= Theorem 1.1, p. 4)

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Synthesis

namespace ReLUSynth.Boolean

/-- Theorem 4.12 (p. 27; Theorem 1.1, p. 4): under either inventory rule, with an affine output,
exact synthesis for a Boolean target supplied by a circuit is `Σ_2^P`-complete under deterministic
polynomial-time many-one reductions; moreover every `Σ_2^P` language reduces to it by such a
reduction whose every image is a well-formed instance with cap `n_max = 4` and a circuit computing
a threshold function with positive rational coefficients. -/
theorem theorem_4_12 (rule : InventoryRule) :
    AvgWorstGap.IsSigmaPComplete 2 (SynthLang rule) ∧
    ∀ L' : Set (List Bool), AvgWorstGap.InSigmaP 2 L' →
      ReducesWithImages L' (SynthLang rule) (fun _ s => ∃ I : SynthInstance,
        s = I.encode ∧ I.WellFormed ∧ I.nmax = 4 ∧ I.C.IsPosThreshold) := by sorry

end ReLUSynth.Boolean
