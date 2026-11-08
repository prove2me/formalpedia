-- Prove2me | Theorems.Thm_QWildMatch_lemma_3_3
-- name    : QWildMatch.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:22.524164+00:00
-- url     : https://prove2.me/theorems/9e591c23-176c-4705-a42c-b873284042f8
-- title:
--   Lemma 3.3 — query composition of a clean mark with bounded-error search
-- statement:
--   There are absolute constants $C,c_0>0$ and $c$ with the following property. Let $V$ be a query circuit with $Q$ queries that, for every oracle $x$ in a family $X$, is a clean mark for $f_x$ on $N$ indices with state-norm error at most $c_0\delta/\sqrt{N+1}$, where $\delta\in(0,1)$. Then there is one query circuit with $Q'$ queries, where
--
--   $$Q'\le C\sqrt{N+1}\;Q\;\bigl(1+\log(N+2)+\log(1/\delta)\bigr)^c,$$
--
--   which for every $x\in X$ outputs, with probability at least $1-\delta$, an index $i$ with $f_x(i)=1$, or "none" when $f_x$ vanishes everywhere.
--
--   This lemma turns a per-index verifier into a search over all indices, and it is the outer loop of the algorithm of Theorem 6.5.
--
--   Differences from the source:
--   - generalization: bounded-error existence search → the find form, which outputs a marked index or none; reason: an existence answer is read off the output, and the witness clause of Theorem 6.5 needs the find form.
--   - generalization: text queries → any finite oracle family $X$ of XOR oracles over any finite abelian group; reason: the text oracle is an instance.
--   - reading: state-norm error $O(\delta/\sqrt{N+1})$ → at most $c_0\delta/\sqrt{N+1}$ with an absolute $c_0>0$; reason: this pins the page's $O$ before the instance.
--   - reading: $\tilde O(\sqrt{N+1}\,Q)$ → $C\sqrt{N+1}\,Q\,\mathrm{polyLog}(N,\delta)^c$ with absolute $C,c$; reason: this pins $\tilde O$ before the instance and includes the logarithmic error reduction the page mentions.
--   - encoding: registers $|x\rangle|z\rangle|0^a\rangle$ → index and target inside the workspace of `QueryAlg`, with an initialized query register $q_0$; reason: this is one layout of the page's registers.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Lemma 3.3, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QWildMatch_IsCleanMark
import Definitions.Def_QWildMatch_polyLog
import Definitions.Def_QWildMatch_SearchCorrect

namespace QWildMatch

open QAlgorithms

/-- Lemma 3.3 (Query composition), Zhao et al., STOC 2027 submission (file sha256 9e87a9dd…), p.4.

**Formalization Note** `c₀` makes the page's `O(δ/√(N + 1))` precise: the hypothesis asks for error at
most `c₀ δ/√(N + 1)` with an absolute `c₀ > 0`. `C`, `c` pin `Õ` with `polyLog N δ`. The circuit `V` is
uniform over the oracle family `X`; `f x` is the mark of oracle `x`. The conclusion is the find form:
output a marked index, or `none` when no index is marked, which is stronger than existence search. The
oracle family is arbitrary, so this applies to the text oracle with `f` the block marks. -/
theorem lemma_3_3 :
    ∃ (C : ℝ) (c : ℕ) (c₀ : ℝ), 0 < C ∧ 0 < c₀ ∧
    ∀ (ι κ W : Type) [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
      [DecidableEq W] [AddCommGroup κ]
      (N Q : ℕ) (X : Set (ι → κ)) (f : (ι → κ) → Fin N → ZMod 2)
      (V : QueryAlg ι κ (Fin N × ZMod 2 × W) Q) (q₀ : ι × κ) (a₀ : W) (δ ε : ℝ),
      0 < δ → δ < 1 → ε ≤ c₀ * δ / √((N : ℝ) + 1) →
      (∀ x ∈ X, IsCleanMark V (xorOracle x) (f x) q₀ a₀ ε) →
    ∃ (N' Q' : ℕ) (A : QueryAlg ι κ (Qubits N') Q')
      (out : ((ι × κ) × Qubits N') → Option (Fin N)),
      (Q' : ℝ) ≤ C * √((N : ℝ) + 1) * (Q : ℝ) * polyLog N δ ^ c ∧
      ∀ x ∈ X, 1 - δ ≤ probEvent (A.finalState (xorOracle x))
        (fun z => SearchCorrect (f x) (out z)) := by sorry

end QWildMatch
