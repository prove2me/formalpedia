-- Prove2me | Theorems.Thm_SDDPConv_Doasa_monotonicity
-- name    : SDDPConv.Doasa.monotonicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:29:57.319185+00:00
-- url     : https://prove2.me/theorems/bea4f3ab-f7d2-4008-b53e-87ba8dd6390b
-- title:
--   §2, p. 4 — the optimal values C^k_t of [AP^k_t] are nondecreasing in k
-- statement:
--   Consider any run of the batched cutting-plane scheme (covering DOASA and DOASA-N) on an instance satisfying (A4). Since cuts are added from one iteration to the next and none is removed, the optimal values of the approximate problems are nondecreasing: for every iteration $k$,
--
--   $$C^{k+1}_1\ \ge\ C^k_1,\qquad C^{k+1}_t(x_{t-1},\omega_{ti})\ \ge\ C^k_t(x_{t-1},\omega_{ti})\quad(t=2,\dots,T),$$
--
--   for every reachable stage-$(t-1)$ decision $x_{t-1}$ and every outcome $\omega_{ti}$. For $t=T$ both sides equal $Q_T(x_{T-1},\omega_{Ti})$.
--
--   Monotonicity is the elementary fact behind every lower-bound argument for cutting-plane methods: the lower bounds $C^k_1$ can only improve.
--
--   **Formalization Note** The paper states the inequality for every $x_{t-1}$; we state it on reachable states, where (A4) makes the approximate problems feasible and bounded (elsewhere the values are junk). The validity of the initial cuts and the oracle specification are not needed. Lean iteration $k$ is the paper's iteration $k+1$.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 4, §2, monotonicity of the optimal values of [AP^k_t]

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run

namespace SDDPConv.Doasa

/-- §2, p. 4: since cuts are only added, the optimal values of the approximate problems are
nondecreasing from one iteration to the next, at every reachable state and outcome. -/
theorem monotonicity (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (sol : Oracle I)
    (F : ℕ → List (Scen I)) (S : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t))
    (hrun : IsBatchRun I L sol F S cuts D) (k : ℕ) :
    apVal I 1 (cutset I cuts k 1) I.b₁ ≤ apVal I 1 (cutset I cuts (k + 1) 1) I.b₁ ∧
      ∀ s, 1 ≤ s → s + 1 ≤ I.T → ∀ x ∈ Reach I s, ∀ i : Fin (I.q (s + 1)),
        apVal I (s + 1) (cutset I cuts k (s + 1)) (rhs I s x i) ≤
          apVal I (s + 1) (cutset I cuts (k + 1) (s + 1)) (rhs I s x i) := by sorry

end SDDPConv.Doasa
