-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_5_8
-- name    : SelectiveDPT.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:37:08.1266+00:00
-- url     : https://prove2.me/theorems/82b6863c-4057-4d01-88a3-1bbe51768ae5
-- title:
--   Theorem 5.8 — list-decoding DPT for $\mathsf{PARITY}_n$: success $\le 2^{-c''k}$ with $c'kn$ queries
-- statement:
--   There are constants $c', c'' > 0$ such that for every $n \ge 1$ and all $k, m \ge 0$, every quantum algorithm for the list-decoding direct product $\mathsf{PARITY}_n^{L(k,m)}$ making at most $c'kn$ queries has success probability
--   $$\Pr[\text{success}] \le 2^{-c''k}.$$
--
--   The algorithm outputs a list of at most $2^{m-k}$ vectors in $\{0,1\}^m$ and succeeds when the list contains the parities of all $m$ inputs; the success probability is averaged over uniformly random inputs.
--
--   Differences from the source:
--   - reading: there are constants c′, c″ > 0 such that any quantum algorithm … → c′, c″ chosen before n, k, m; reason: the constants are absolute
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, uniform on {0,1}^n (p.32); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - encoding: n arbitrary → 0 < n; reason: at n = 0 no query algorithm exists (the query register Fin m × Fin 0 is empty), so the statement would be vacuous; PARITY_0 is also a constant function
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - generalization: f^{L(k,m)} for k ≤ m → all naturals k, m; reason: for k > m and |Y| ≥ 2 only the empty list meets the size bound and it is never correct, so the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 5.8, p.45

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_Supplement_parityFn
import Definitions.Def_SelectiveDPT_Supplement_listRel

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 5.8 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.45: there are constants
`c′, c″ > 0` such that any quantum algorithm for `PARITY_n^{L(k,m)}` with at most `c′kn` queries has
success probability at most `2^{−c″k}`.

**Formalization Note.** `c′, c″` are chosen before `n`, `k`, `m`. The success probability is the
average over the uniform distribution on `({0,1}^n)^m` (proof of Theorem 1.7, p.32). The output is
a list of at most `2^{m−k}` vectors in `{0,1}^m` (`listRel`). `0 < n`: at `n = 0` no query
algorithm exists. `k`, `m` arbitrary. -/
theorem theorem_5_8 :
    ∃ c' c'' : ℝ, 0 < c' ∧ 0 < c'' ∧ ∀ (n : ℕ), 0 < n → ∀ (k m b T : ℕ)
      (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
      (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → ZMod 2)),
      (T : ℝ) ≤ c' * k * n →
      ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
          prodDist (parityDist n) m x *
            successProb A out (listRel k m (fun x y => parityFn n x = y)) x ≤
        (2 : ℝ) ^ (-(c'' * k)) := by sorry

end SelectiveDPT.Supplement
