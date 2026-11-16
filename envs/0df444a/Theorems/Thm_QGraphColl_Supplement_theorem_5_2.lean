-- Prove2me | Theorems.Thm_QGraphColl_Supplement_theorem_5_2
-- name    : QGraphColl.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:32:52.280205+00:00
-- url     : https://prove2.me/theorems/c54ec7de-18f3-4899-a60d-4f0baabf2e9e
-- title:
--   Theorem 5.2 — $Q_2(f)=\tilde O((nq)^{11/17})$ for partial functions over an alphabet of size $q$ with $C_1(f)\le2$
-- statement:
--   There are absolute constants $C>0$ and $K\ge0$ with the following property. Let $n\ge1$ and $q\ge1$, let $\Sigma=\{0,\dots,q-1\}$, let $D\subseteq\Sigma^n$ and let $f:D\to\{0,1\}$ be a (partial) function whose positive certificate complexity satisfies $C_1(f)\le2$. Then there is a quantum query algorithm with
--   $$T\ \le\ C\,(nq)^{11/17}\,\bigl(\log_2(nq+2)\bigr)^K$$
--   queries to the $q$-ary standard oracle $|i,c\rangle\mapsto|i,\,c+x_i \bmod q\rangle$ that, for every $x\in D$, outputs $f(x)$ with probability at least $2/3$. In other words $Q_2(f)=\tilde O\bigl((nq)^{11/17}\bigr)$.
--
--   The bound contrasts with the $\Omega(n^{2/3})$ lower bound for element distinctness over large alphabets, whose positive inputs also have certificates of size two: it is $o(n^{2/3})$ whenever $q=O(n^{1/33-\varepsilon})$, so the alphabet size matters in lower bounds based on certificate structure.
--
--   **Formalization Note** The algorithm is a `QueryAlg (Fin n) (Fin q) (Fin m) T` with `xorOracle x` over `Fin q`, and correctness is `Supplement.ComputesOn … D f (1/3)`; $C$ and $K$ are chosen before $n$, $q$, $D$ and $f$.
--
--   Differences from the source:
--   - encoding: an alphabet Σ with |Σ| = q → Fin q (q ≥ 1) with addition mod q in the oracle; reason: any alphabet of size q relabels bijectively to Fin q; the paper's q-ary queries read one symbol x_i per query
--   - encoding: Q₂(f) = Õ((nq)^{11/17}) → ∃ absolute C > 0, K ≥ 0 with an algorithm of T ≤ C·(nq)^{11/17}·(log₂(nq+2))^K queries and error ≤ 1/3 on every x ∈ D; reason: Q₂ is the least cost of such an algorithm; Õ suppresses polylog factors; the paper's proof applies Theorem 1.1 on nq vertices, so its log is log(nq); the + 2 keeps the factor positive at n = q = 1, and when q ≥ n^{6/11} the trivial bound n ≤ (nq)^{11/17} needs no log at all, so polylog(n) and polylog(nq) give the same class
--   - encoding: D ⊆ Σ^n for every n → n ≥ 1; reason: for n = 0 the query register Fin 0 × Fin q is empty and the query model has no algorithm object; the paper's footnote (p.31) covers n = 1, which is included
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Theorem 5.2, p.32 (definitions of C1(f) and Q2(f) p.31; footnote 1 p.31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_Supplement_C1
import Definitions.Def_QGraphColl_Supplement_ComputesOn

open QAlgorithms

namespace QGraphColl.Supplement

/-- **Theorem 5.2** (Query bound for an arbitrary alphabet; A. Cornelissen, A. S. Gilani,
S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum barriers for Graph Collision*,
arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.32): let `f : D → {0,1}` be a
(partial) function, where `D ⊆ Σⁿ`, `|Σ| = q`, and `C₁(f) ≤ 2`. Then `Q₂(f) = Õ((nq)^{11/17})`.

**Formalization Note.**
* The alphabet is `Fin q` (`q ≥ 1`, as `NeZero q`); any alphabet of size `q` relabels to it. One
  query is the `q`-ary standard query `|i, c⟩ ↦ |i, c + x_i mod q⟩` (`xorOracle x` over `Fin q`).
* `D` is a promise: correctness is required, and `C₁(f)` is computed, only on inputs in `D`.
* `Q₂(f) = Õ((nq)^{11/17})` is: there are absolute constants `C > 0`, `K ≥ 0` (chosen before
  `n`, `q`, `D`, `f`) such that some `T`-query algorithm with
  `T ≤ C · (nq)^{11/17} · (log₂(nq + 2))^K` computes `f` on `D` with error at most `1/3`
  on every input of `D`. The `+ 2` keeps the logarithm positive at `n = q = 1`.
* `n ≥ 1`: for `n = 0` the query register `Fin 0 × Fin q` is empty and no algorithm object
  exists; the paper's footnote (p.31) covers `n = 1`, which is included. -/
theorem theorem_5_2 :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (n q : ℕ) [NeZero q], 1 ≤ n →
      ∀ (D : Finset (Fin n → Fin q)) (f : (Fin n → Fin q) → Bool), C1 D f ≤ 2 →
        ∃ T : ℕ,
          (T : ℝ) ≤ C * ((n : ℝ) * q) ^ ((11 : ℝ) / 17) * Real.logb 2 ((n : ℝ) * q + 2) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg (Fin n) (Fin q) (Fin m) T)
            (out : (Fin n × Fin q) × Fin m → Bool),
            ComputesOn A out D f (1 / 3) := by sorry

end QGraphColl.Supplement
