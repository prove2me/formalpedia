-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_1_7
-- name    : SelectiveDPT.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:30:48.575318+00:00
-- url     : https://prove2.me/theorems/1dab4ab4-6ee4-4c9e-96df-329d90eba846
-- title:
--   Theorem 1.7 — selective DPT for $\mathsf{PARITY}_n$: success $\le 2^{k(2H_2(p)-1+p)}$, and $\le 2^{-k/4}$ when $T\le kn/32$
-- statement:
--   Let $n \ge 1$ and $k, m \ge 0$. Every quantum query algorithm for the selective direct product $\mathsf{PARITY}_n^{(k,m)}$ that makes $T \le kn/4$ queries has success probability
--   $$\Pr[\text{success}] \le 2^{k(2H_2(p) - 1 + p)}, \qquad p = \frac{2T}{kn},$$
--   where $H_2$ is the binary entropy function. In particular, if $T \le kn/32$ then
--   $$\Pr[\text{success}] \le 2^{-k/4}.$$
--
--   The algorithm outputs $k$ pairs (copy, bit) with pairwise distinct copies of its choice and succeeds when every bit is the parity of its copy; the success probability is averaged over uniformly random inputs. Since $kn/2$ queries suffice to solve $k$ copies exactly, the bound is tight up to constants.
--
--   Differences from the source:
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, uniform on {0,1}^n (p.32); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - encoding: n arbitrary → 0 < n; reason: at n = 0 no query algorithm exists (the query register Fin m × Fin 0 is empty), so the statement would be vacuous; p = 2T/(kn) is also undefined there
--   - encoding: p = 2T/(kn) (k ≥ 1 implicit) → p = 2T/(kn) for every natural k, with Lean's 0/0 = 0; reason: at k = 0 the hypothesis forces T = 0, p = 0 and both bounds equal 1, so no instance changes
--   - generalization: f^(k,m) for k ≤ m (Definition 1.1) → all naturals k, m; reason: for k > m no output has k distinct copies, so the success probability is 0 and the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.7, p.5 (restated p.32)

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_selRel
import Definitions.Def_SelectiveDPT_H2
import Definitions.Def_SelectiveDPT_Supplement_parityFn

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 1.7 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.5 (restated p.32): every
quantum query algorithm solving `PARITY_n^(k,m)` with `T ≤ kn/4` queries has success probability
at most `2^{k(2H₂(p) − 1 + p)}`, where `H₂` is the binary entropy function and `p = 2T/(kn)`. In
particular, if `T ≤ kn/32`, then the success probability is at most `2^{−k/4}`.

**Formalization Note.** Both clauses are stated. The success probability is the average over
the uniform distribution on `({0,1}^n)^m` (proof of Theorem 1.7, p.32). `0 < n`: at `n = 0`,
`p = 2T/0` is undefined, and no query algorithm exists (empty query register). `k` is arbitrary:
at `k = 0` the hypothesis forces `T = 0`, Lean's `p = 0/0 = 0` and both bounds are `1`. `H₂` is in
bits (base `H2`). Outputs are `k` (copy, bit) pairs with distinct copies (base `selRel`). -/
theorem theorem_1_7 (n : ℕ) (hn : 0 < n) (k m b T : ℕ)
    (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
    (out : ((Fin m × Fin n) × ZMod 2) × Fin b → (Fin k → Fin m × ZMod 2))
    (hT : (T : ℝ) ≤ k * n / 4) :
    let p : ℝ := 2 * T / (k * n)
    let succ : ℝ := ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
        prodDist (parityDist n) m x * successProb A out (selRel k m (fun x y => parityFn n x = y)) x
    succ ≤ (2 : ℝ) ^ (k * (2 * H2 p - 1 + p)) ∧
      ((T : ℝ) ≤ k * n / 32 → succ ≤ (2 : ℝ) ^ (-(k : ℝ) / 4)) := by sorry

end SelectiveDPT.Supplement
