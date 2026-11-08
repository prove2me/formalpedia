-- Prove2me | Theorems.Thm_QWildMatch_theorem_6_5
-- name    : QWildMatch.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:18:10.187656+00:00
-- url     : https://prove2.me/theorems/eb1c8c3e-377e-4e33-9469-5f62707bb97f
-- title:
--   Theorem 6.5 — sparse-periodic weighted wildcard algorithm with $\tilde O(\sqrt{\lceil (n+1)/L\rceil}\sqrt{(L+\ell)(q+1)})$ text queries
-- statement:
--   Let $\Sigma$ be a finite nonempty alphabet with an injective encoding into bit strings, let $T\in\Sigma^n$ be a text and $P\in(\Sigma\cup\{\star\})^m$ a pattern, with arbitrary nonnegative substitution costs and positive character-dependent gap costs. Let $k\ge0$, $L\ge1$, $q\ge0$, $\delta\in(0,1)$, and let references $B_b$ be given for the $N_B=\lceil(n+1)/L\rceil$ blocks. Put $\ell=m+\lfloor k/\alpha\rfloor$.
--
--   There are absolute constants $C>0$ and $c$ and, for these classical inputs, one quantum query algorithm making $Q_T$ text queries with
--
--   $$Q_T\le C\,\sqrt{\lceil(n+1)/L\rceil}\,\sqrt{(L+\ell)(q+1)}\,\bigl(1+\log(n+2)+\log(1/\delta)\bigr)^c,$$
--
--   such that on every text $T$ satisfying the sparse-defect promise of Assumption 6.1, with probability at least $1-\delta$, the output is correct: either a witness $(s,e)$ with $0\le s\le e\le n$ together with an edit script of $P$ into $T[s:e]$ of cost at most $k$ (so $\mathrm{ED}_\mu(P,T[s:e])\le k$), or "none" when no such pair exists.
--
--   Moreover, for all constants $c_1>0$ and $c_2$ there is a constant $C'$, depending only on them, such that whenever $c_1\ell\le L\le c_2\ell$ and $\ell\le n$, the same algorithm satisfies
--
--   $$Q_T\le C'\sqrt{(n+1)(q+1)}\,\bigl(1+\log(n+2)+\log(1/\delta)\bigr)^c.$$
--
--   The theorem says that for texts close to a known background the query cost depends on $n$ and on the number of defects, and no longer on $m$ and $k$ when blocks have length comparable to the candidate window. It makes no claim about running time or about texts outside the promise.
--
--   **Formalization Note** The query model is the non-uniform `QueryAlg`: the unitaries and the output map may depend on every classical input, but not on $T$.
--
--   Differences from the source:
--   - reading: $\tilde O(\cdots\mathrm{polylog}(1/\delta))$ in (2) → $C\cdots(1+\log(n+2)+\log(1/\delta))^c$ with absolute $C,c$ fixed before every instance parameter; reason: this pins $\tilde O$, and the printed $\mathrm{polylog}(1/\delta)$ is part of the same factor.
--   - reading: when $n\ge\ell$ and $L=\Theta(\ell)$ → for all $c_1>0$ and $c_2$ there is $C'$ with the bound whenever $c_1\ell\le L\le c_2\ell$ and $\ell\le n$; reason: this is the standard meaning of $\Theta$, with the implied constants chosen first.
--   - reading: a quantum algorithm for the classical input → a non-uniform `QueryAlg` chosen after every classical input and before $T$; reason: the page treats the references as supplied input and charges their gate costs to time, not queries.
--   - reading: consecutive blocks of at most $L$ starts → the partition $bL\le s<(b+1)L$; reason: the page does not name a partition, and this is the canonical one.
--   - generalization: a witness of $(s,e)$ and, when requested, a valid edit script → the output $(s,e)$ together with an edit script of cost at most $k$, always; reason: always outputting the script covers every request, and dropping it gives the $(s,e)$-only output.
--   - generalization: §3 fixes $\mu(\star,b)=0$ and $\mu(a,a)=0$ → Lean takes any $\mu\ge0$; reason: Theorem 6.5 says nonnegative character-dependent substitutions, and a table satisfying the equations is an instance.
--   - generalization: the witness with the charged additional resource cost → the witness inside the bound (2); reason: one more list reconstruction for the found block stays within (2), and the rest is classical.
--   - encoding: the periodic function $B_b:J_b\to\Sigma$ → an arbitrary function; reason: every function on the finite interval $J_b$ is periodic with period its length, and §6 uses no period.
--   - encoding: $O_T:|j,z\rangle\mapsto|j,z\oplus T[j]\rangle$ → `xorOracle` on `Option (Fin n)` and `Fin w → ZMod 2` through an injective `enc`; reason: `none` answers $0$, which keeps $n=0$ and makes a query skippable, and characteristic 2 makes an inverse call one query.
--   - encoding: a threshold $k$ → the hypothesis $k\ge0$; reason: for $k<0$ no alignment exists and the problem is empty.
--   - encoding: the minimum $\mathrm{ED}_\mu\le k$ → some grid path has cost at most $k$; reason: the minimum over a finite nonempty set of paths is at most $k$ exactly when some path is.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Theorem 6.5, eq. (2), p.10; Assumption 6.1, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QWildMatch_Match
import Definitions.Def_QWildMatch_SparsePromise
import Definitions.Def_QWildMatch_textOracle
import Definitions.Def_QWildMatch_polyLog

namespace QWildMatch

open QAlgorithms

/-- Theorem 6.5 (Sparse-periodic weighted wildcard algorithm), Zhao et al., STOC 2027 submission (file
sha256 9e87a9dd…), p.10, all clauses: bound (2), the simplification for `n ≥ ℓ` and `L = Θ(ℓ)`, and the
witness.

**Formalization Note** `Õ` is pinned: `C`, `c` are absolute and precede every instance parameter, with
`polyLog n δ = 1 + log(n + 2) + log(1/δ)`. `L = Θ(ℓ)` is `c₁ ℓ ≤ L ≤ c₂ ℓ`, and `C'` depends on `c₁`, `c₂`
only. The query model is the non-uniform `QueryAlg`: the circuit and `out` may depend on every classical
input (alphabet, encoding, costs, pattern, `k`, `L`, `q`, the references `B`, `δ`), never on `T`. The
witness is `out`'s `some (s, e, o)`, with the edit script `o`, charged inside bound (2). The reference is an arbitrary function; the
page's "periodic" is vacuous on a finite interval. -/
theorem theorem_6_5 :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C' : ℝ, 0 < C' ∧
    ∀ (Sym : Type) [Fintype Sym] [DecidableEq Sym] [Nonempty Sym]
      (w : ℕ) (enc : Sym → (Fin w → ZMod 2)), Function.Injective enc →
    ∀ (cm : CostModel Sym) (n : ℕ) (P : List (Option Sym)) (k : ℝ), 0 ≤ k →
    ∀ (L q : ℕ), 1 ≤ L → ∀ (B : ℕ → Fin n → Sym) (δ : ℝ), 0 < δ → δ < 1 →
    ∃ (N Q : ℕ) (A : QueryAlg (Option (Fin n)) (Fin w → ZMod 2) (Qubits N) Q)
      (out : ((Option (Fin n) × (Fin w → ZMod 2)) × Qubits N) → Option (ℕ × ℕ × List Op)),
      (Q : ℝ) ≤ C * √(NB n L : ℝ) * √(((L : ℝ) + (ell cm P k : ℝ)) * ((q : ℝ) + 1)) *
        polyLog n δ ^ c ∧
      ((c₁ * (ell cm P k : ℝ) ≤ (L : ℝ) ∧ (L : ℝ) ≤ c₂ * (ell cm P k : ℝ) ∧ ell cm P k ≤ n) →
        (Q : ℝ) ≤ C' * √(((n : ℝ) + 1) * ((q : ℝ) + 1)) * polyLog n δ ^ c) ∧
      ∀ T : Fin n → Sym, SparsePromise n L (ell cm P k) q B T →
        1 - δ ≤ probEvent (A.finalState (textOracle enc T))
          (fun z => Correct cm P T k (out z)) := by sorry

end QWildMatch
