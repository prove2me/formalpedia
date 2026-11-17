-- Prove2me | Theorems.Thm_QWildMatch_Supplement_theorem_1_1
-- name    : QWildMatch.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:21:36.050047+00:00
-- url     : https://prove2.me/theorems/5a31fa54-3aeb-48c0-b628-fe57260f9d6e
-- title:
--   Theorem 1.1 (formal version, Corollary 4.2) — arbitrary-text baseline: $\tilde O(\sqrt{n+1}\,(m+r_++1))$ queries with a minimum-cost witness
-- statement:
--   Let $\Sigma$ be a finite nonempty alphabet, $P\in(\Sigma\cup\{\star\})^m$ a wildcard pattern, $\mu\ge0$, $c_{\mathrm{del}}>0$, $c_{\mathrm{ins}}>0$ a cost table, $k$ a threshold, $\alpha$ the minimum insertion cost and $r_+=\lfloor k/\alpha\rfloor$. There are absolute constants $C>0$ and $c$ such that for every $n$ and every $\delta\in(0,1)$ there is a quantum algorithm making
--   $$Q\le C\,\sqrt{n+1}\,(m+r_++1)\,\big(1+\log(n+2)+\log(1/\delta)\big)^{c}$$
--   queries to the text oracle $O_T$ that, on **every** text $T\in\Sigma^n$, with probability at least $1-\delta$:
--
--   1. outputs "no match" only if no substring $T[s:e]$ has $\mathrm{ED}_\mu(P,T[s:e])\le k$;
--   2. otherwise outputs a start $s$, an end $e$ with $s\le e\le n$ and an edit script for $T[s:e]$ of minimum cost, which is at most $k$.
--
--   No promise on the text is assumed. This is the unconditional baseline against which the sparse-periodic algorithm of Theorem 6.5, the mission's goal, is measured: it searches over the $n+1$ starts with the fixed-start verifier of Theorem 4.1.
--
--   **Formalization Note** The query model is the base mission's: a non-uniform `QueryAlg` with the published `textOracle`, which may depend on every classical input but not on $T$.
--
--   Differences from the source:
--   - reading: Theorem 1.1 (informal): decides with O(√(n + 1)(m + r₊ + 1)) queries 'up to logarithmic amplification factors' → its formal version Corollary 4.2: the output is none (no match) or a witness (s, e, o) with a minimum-cost edit script o of cost ≤ k, correct with probability ≥ 1 − δ on every text; reason: Section 4 is named on p.2 as the formal statement; Corollary 4.2 adds the start, endpoint and minimum-cost script, which imply the decision
--   - reading: bounded error, Õ(√(n + 1)(m + r₊ + 1)) → for every δ ∈ (0, 1), Q ≤ C·√(n + 1)·(m + r₊ + 1)·polyLog(n, δ)^c with C, c absolute and before every instance parameter, polyLog(n, δ) = 1 + log(n + 2) + log(1/δ); reason: the base mission's reading of Õ and of the error parameter (Theorem 6.5); δ = 1/3 gives bounded error
--   - generalization: witness recovery 'incurs additional gate and, if the DP must be recomputed, text-query cost' (proof of Corollary 4.2) → the witness with its minimum-cost script is charged inside the same query bound; reason: recomputing the DP for the found start reads at most m + r₊ symbols again, within the bound; the statement implies the decision version
--   - generalization: threshold k (implicitly k ≥ 0) → any real k; reason: for k < 0 nothing matches and the output none is correct with 0 queries; the case k ≥ 0 is the source's
--   - encoding: quantum text-query algorithm with oracle O_T → QueryAlg with the published textOracle (index Option (Fin n), none answering 0; symbols through an injective enc : Σ → (ZMod 2)^w); circuit and output map may depend on every classical input, never on T; reason: the base mission's query model
--   - generalization: cost table with μ(⋆, b) = 0 and μ(a, a) = 0 (§3, p.3) → any CostModel (μ ≥ 0, gaps > 0), IsWildcardCost not assumed; reason: the search over starts and the banded DP use only nonnegativity of μ and positivity of the gaps; the §3 tables are special cases
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Theorem 1.1, p.2; formal version Corollary 4.2, p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QWildMatch_Match
import Definitions.Def_QWildMatch_textOracle
import Definitions.Def_QWildMatch_polyLog
import Definitions.Def_QWildMatch_Supplement_CorrectMin

namespace QWildMatch.Supplement

open QAlgorithms QWildMatch

/-- Theorem 1.1 (Unrestricted baseline), Zhao, Chen, Li, Kong, Peng, Yu, Yue, STOC 2027 submission (file
sha256 9e87a9dd…), p.2, stated at the strength of its formal version Corollary 4.2 (Arbitrary-text quantum
baseline), p.5: for arbitrary texts, `Õ(√(n + 1) (m + r₊ + 1))` text queries decide weighted wildcard
substring existence with bounded error, and on YES instances output a start, an endpoint and a
minimum-cost edit script.

**Formalization Note** `Õ` is pinned as in the base mission: `C`, `c` are absolute and precede every
instance parameter, the error is any `δ ∈ (0, 1)`, and the factor is `polyLog n δ ^ c`. The query model is
the non-uniform `QueryAlg` with the base mission's `textOracle`: the circuit and `out` may depend on every
classical input but never on `T`. The witness, with a minimum-cost script, is charged inside the bound. -/
theorem theorem_1_1 :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (Sym : Type) [Fintype Sym] [DecidableEq Sym] [Nonempty Sym]
      (w : ℕ) (enc : Sym → (Fin w → ZMod 2)), Function.Injective enc →
    ∀ (cm : CostModel Sym) (n : ℕ) (P : List (Option Sym)) (k δ : ℝ), 0 < δ → δ < 1 →
    ∃ (N Q : ℕ) (A : QueryAlg (Option (Fin n)) (Fin w → ZMod 2) (Qubits N) Q)
      (out : ((Option (Fin n) × (Fin w → ZMod 2)) × Qubits N) → Option (ℕ × ℕ × List Op)),
      (Q : ℝ) ≤ C * √((n : ℝ) + 1) * ((P.length : ℝ) + (rPlus cm k : ℝ) + 1) * polyLog n δ ^ c ∧
      ∀ T : Fin n → Sym,
        1 - δ ≤ probEvent (A.finalState (textOracle enc T)) (fun z => CorrectMin cm P T k (out z)) := by sorry

end QWildMatch.Supplement
