-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_25_2_2
-- name    : WildeQIT.Compression.Supplement.theorem_25_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:21:14.940001+00:00
-- url     : https://prove2.me/theorems/ab66e9ad-2839-5c6e-82a0-b1a4447302b4
-- title:
--   Theorem 25.2.2 (Holevo–Schumacher–Westmoreland): $\mathcal C_C(\mathcal N)=\overline{\bigcup_k\frac1k\mathcal C^{(1)}_C(\mathcal N^{\otimes k})}$
-- statement:
--   The classical capacity region of a quantum channel $\mathcal N$ is
--
--   $$
--   \mathcal C_C(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\,\mathcal C^{(1)}_C(\mathcal N^{\otimes k})},
--   $$
--
--   where $\mathcal C^{(1)}_C(\mathcal N)$ is the union over states $\sigma_{XAB}$ of the form (25.11) of the sets of all $C\ge0$ with $C\le I(X;B)_\sigma+I(A\rangle BX)_\sigma$, and $\mathcal C_C(\mathcal N)=\{C\ge0:(C,0,0)\in\mathcal C_{CQE}(\mathcal N)\}$.
--
--   The state $\sigma_{XAB}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\varphi^x_{AA'})$ has pure $\varphi^x_{AA'}$; on $k$ channel uses the inputs are states on $A'^k$. The theorem is a special case of the quantum dynamic capacity theorem (Theorem 25.2.1).
--
--   **Formalization Note** $\mathcal C_{CQE}(\mathcal N)$ is `operationalDynamicRegion` of the published `Claimed50.P20`; channels are superoperators with `IsChannel`, and $k$ uses of the channel are `piSuperop`. The closure is outside the union.
--
--   Differences from the source:
--   - encoding: the scenario region defined in words on p. 698 ("the achievable rate region lies on the (C, 0, 0) ray …") → the slice of Claimed50.P20.operationalDynamicRegion (C_CQE of Theorem 25.2.1, the closure of the achievable rate triples) with nonnegative rates; reason: the book defines the five regions only as these rays and quarter-planes of C_CQE(N), "the union of all achievable rates" (p. 696); the Lean region is the one of the referenced Theorem 25.2.1, and its closure adds only limits of achievable triples, which the δ-slack definition of achievability already admits
--   - encoding: (1/k) C^(1)(N^{⊗k}), states on A′^k → {x | k • x ∈ C^(1)(piSuperop (fun _ : Fin k => N))}, k ≥ 1; reason: the scaled set written by membership; piSuperop is k uses of the channel on A′^k
--   - encoding: a quantum channel on Hilbert spaces → `IsChannel N` with nonempty input and output types; reason: the setting of the referenced Claimed50.P20; zero-dimensional spaces carry no state
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.2.2, p. 698, eqs. (25.17)–(25.18); §25.2.1, p. 698

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_classicalRegion
import Definitions.Def_WildeQIT_Compression_Supplement_oneShotClassicalRegion

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.2, p. 698.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Theorem 25.2.2 (Holevo–Schumacher–Westmoreland)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 698, (25.17)–(25.18)): "The classical capacity region `C_C(N)` is given by `C_C(N) = closure ∪_{k≥1} (1/k) C^(1)_C(N^{⊗k})`. The region `C^(1)_C(N)` is the union of the state-dependent regions `C^(1)_{C,σ}(N)`, where `C^(1)_{C,σ}(N)` is the set of all `C ≥ 0`, such that `C ≤ I(X;B)_σ + I(A⟩BX)_σ`."

Formalization Note: `N` is a quantum channel on nonempty finite systems as in the published
`Claimed50.P20` (whose `operationalDynamicRegion` is `C_CQE(N)`, the region of Theorem 25.2.1).
`(1/k) S` is written `{x | k • x ∈ S}`, with `k ≥ 1`; on `k` uses the channel is
`piSuperop (fun _ : Fin k => N)` and its inputs are states on `A′^k`, as the book requires. The
closure is outside the union. -/
theorem theorem_25_2_2 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    classicalRegion N = closure {x : ℝ | ∃ k : ℕ, 0 < k ∧
      (k : ℝ) * x ∈ oneShotClassicalRegion (piSuperop (fun _ : Fin k => N))} := by sorry

end WildeQIT.Compression.Supplement
