-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_5_7
-- name    : SelectiveDPT.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:36:37.028379+00:00
-- url     : https://prove2.me/theorems/aea87233-8d93-4dcb-a8f2-82566bade258
-- title:
--   Theorem 5.7 — list-decoding DPT for $\mathsf{OR}_n$: success $\le 9\cdot2^{-k/4}$ with $k\sqrt n/144$ queries
-- statement:
--   Let $n \ge 1$ and $k, m \ge 0$. Every quantum algorithm for the list-decoding direct product $\mathsf{OR}_n^{L(k,m)}$ making at most
--   $$\frac{k\sqrt n}{144}$$
--   queries has success probability
--   $$\Pr[\text{success}] \le 9 \cdot 2^{-k/4}.$$
--
--   The algorithm outputs a list of at most $2^{m-k}$ vectors in $\{0,1\}^m$ and succeeds when the list contains $(\mathsf{OR}_n(x_1), \dots, \mathsf{OR}_n(x_m))$; the success probability is averaged over $m$ independent inputs from the hard distribution of $\mathsf{OR}_n$ ($1/2$ on $0^n$, $1/(2n)$ on each weight-one string).
--
--   Differences from the source:
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, 1/2 on 0^n and 1/(2n) on each weight-one string (§4.1.2, p.30); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - encoding: n arbitrary → 0 < n; reason: at n = 0 no query algorithm exists (the query register Fin m × Fin 0 is empty), so the statement would be vacuous; the hard distribution is also undefined there
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - generalization: f^{L(k,m)} for k ≤ m → all naturals k, m; reason: for k > m and |Y| ≥ 2 only the empty list meets the size bound and it is never correct, so the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 5.7, p.45

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_Supplement_orFn
import Definitions.Def_SelectiveDPT_Supplement_listRel

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 5.7 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.45: any quantum algorithm for
`OR_n^{L(k,m)}` with at most `k√n/144` queries has success probability at most `9 · 2^{−k/4}`.

**Formalization Note.** The success probability is the average over `m` independent copies of
the hard distribution of `OR_n` (§4.1.2: `1/2` on `0^n`, `1/(2n)` on each weight-`1` string). The
output is a list of at most `2^{m−k}` vectors in `{0,1}^m` (`listRel`). `0 < n`: at `n = 0` that
distribution is undefined and no query algorithm exists. `k`, `m` arbitrary. -/
theorem theorem_5_7 (n : ℕ) (hn : 0 < n) (k m b T : ℕ)
    (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
    (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → ZMod 2))
    (hT : (T : ℝ) ≤ k * Real.sqrt n / 144) :
    ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
        prodDist (orDist n) m x * successProb A out (listRel k m (fun x y => orFn n x = y)) x ≤
      9 * (2 : ℝ) ^ (-(k : ℝ) / 4) := by sorry

end SelectiveDPT.Supplement
