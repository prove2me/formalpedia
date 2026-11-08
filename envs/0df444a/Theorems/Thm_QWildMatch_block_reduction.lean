-- Prove2me | Theorems.Thm_QWildMatch_block_reduction
-- name    : QWildMatch.block_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:18:00.745351+00:00
-- url     : https://prove2.me/theorems/d0af6939-0933-4aee-b86d-1b7fda5664d5
-- title:
--   Proof of Theorem 6.5 — reconstruction from a correct list decides $\mathrm{Match}$ block by block
-- statement:
--   Let $L\ge1$ and $\ell=m+r_+$, and let $\tilde T_b$ be the reconstruction of the text from the reference $B_b$ and the true list $\mathrm{List}_b$. Then:
--
--   1. $\tilde T_b(x)=T(x)$ for every $x\in J_b$;
--   2. for every start $s\in I_b$, the fixed-start predicate on $\tilde T_b$ agrees with the one on $T$;
--   3. $\mathrm{Match}(P,T,k)$ holds if and only if there are $b<N_B$ and $s\in I_b$ such that the fixed-start predicate holds on $\tilde T_b$ at $s$.
--
--   So a correct list reduces the substring decision to a classical computation per block, with no further text queries.
--
--   **Formalization Note** No promise is needed here: the list is the true one, whatever its size. The promise is what produces that list within the query budget.
--
--   Differences from the source:
--   - generalization: §3 fixes $\mu(\star,b)=0$ and $\mu(a,a)=0$ → Lean takes any $\mu\ge0$; reason: the argument uses neither equation.
--   - generalization: on the promised inputs → for every reference and every text; reason: a correct list is all the argument uses, and promised inputs are an instance.
--   - reading: consecutive blocks of at most $L$ starts → the partition $bL\le s<(b+1)L$; reason: the page does not name a partition, and this is the canonical one.
--   - encoding: $\mathrm{List}_b$ with sorted positions, count and padding → the `Finset` of pairs $(x,T[x])$; reason: these are encodings of the same set.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §6.3, pp.9–10; Proof of Theorem 6.5, p.10

import Mathlib
import Definitions.Def_QWildMatch_Match
import Definitions.Def_QWildMatch_SparsePromise

namespace QWildMatch

/-- The block decision of the proof of Theorem 6.5, Zhao et al., STOC 2027 submission (file sha256
9e87a9dd…), p.10: the reconstruction from a correct list equals the text on `J_b`, the fixed-start
predicate on the reconstruction equals the one on the text for every start of the block, and so the
OR over the blocks and their starts is `Match`.

**Formalization Note** No promise is needed: the list here is the true `List_b`. The promise only
serves to produce it within the query budget. `k ≥ 0` is not needed either: for `k < 0` no path has
cost at most `k` and both sides are false. -/
theorem block_reduction {Sym : Type} [Fintype Sym] [DecidableEq Sym] [Nonempty Sym] {n : ℕ}
    (cm : CostModel Sym) (P : List (Option Sym)) (k : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (B : ℕ → Fin n → Sym) (T : Fin n → Sym) :
    (∀ b : ℕ, ∀ x ∈ J n L (ell cm P k) b,
      recon B b (defectList n L (ell cm P k) B b T) x = T x) ∧
    (∀ b : ℕ, ∀ s ∈ I n L b,
      (FixedStart cm P (recon B b (defectList n L (ell cm P k) B b T)) k s ↔
        FixedStart cm P T k s)) ∧
    (Match cm P T k ↔ ∃ b : ℕ, b < NB n L ∧ ∃ s ∈ I n L b,
      FixedStart cm P (recon B b (defectList n L (ell cm P k) B b T)) k s) := by sorry

end QWildMatch
