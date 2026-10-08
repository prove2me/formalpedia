-- Prove2me | Theorems.Thm_SDDPConv_Doasa_lowerBound
-- name    : SDDPConv.Doasa.lowerBound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:30:39.329456+00:00
-- url     : https://prove2.me/theorems/43baafda-3512-4bc9-bf73-bec25b8a8a85
-- title:
--   §2, p. 4 — every cut is a valid lower bound: C^k_t ≤ Q_t and C^k_1 ≤ Q_1
-- statement:
--   Consider any run of the batched cutting-plane scheme on an instance satisfying (A4), started from valid initial cuts ($L_t\le\mathcal Q_{t+1}(x_t)$ on reachable states). Then the polyhedral approximation stays below the true cost-to-go:
--
--   1. every cut $(\alpha,\beta)$ in the stage-$t$ cut set of every iteration satisfies $\alpha-\beta^\top x_t\le\mathcal Q_{t+1}(x_t)$ for every reachable $x_t$, $1\le t\le T-1$;
--   2. hence, for $2\le t\le T$, every reachable $x_{t-1}$ and every outcome $\omega_{ti}$,
--   $$C^k_t(x_{t-1},\omega_{ti})\ \le\ Q_t(x_{t-1},\omega_{ti});$$
--   3. and for every $k$, $C^k_1\le Q_1$: the optimal value of [AP$^k_1$] is a lower bound on the optimal expected cost of [LP1].
--
--   This is what makes $C^k_1$ a certified lower bound in SDDP-type methods, used to stop the algorithm when a simulated policy cost is close enough.
--
--   **Formalization Note** The paper's trivial initial cut $\theta\ge-\infty$ is replaced by the finite cut $(L_t,0)$; its validity is the hypothesis `ValidInit`, without which the statement fails. Statements are on reachable states (see the `Model` definition). The oracle specification is not needed.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 4, §2, [AP^k_t] approximates [LP_t] from below; p. 10, last sentence of the proof of Lemma 2

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run

namespace SDDPConv.Doasa

/-- §2, p. 4, and Lemma 2's last sentence, p. 10: every cut ever generated is a valid lower
bound on the expected cost-to-go at reachable states, hence the optimal value of each approximate
problem is a lower bound on that of the corresponding [LP_t], and `C^k_1 ≤ Q_1` for every `k`. -/
theorem lowerBound (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (hL : ValidInit I L) (sol : Oracle I)
    (F : ℕ → List (Scen I)) (S : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t))
    (hrun : IsBatchRun I L sol F S cuts D) :
    (∀ k s, 1 ≤ s → s + 1 ≤ I.T → ∀ a ∈ cutset I cuts k s, ∀ x ∈ Reach I s,
        a.eval I x ≤ V I s x) ∧
      (∀ k s, 1 ≤ s → s + 1 ≤ I.T → ∀ x ∈ Reach I s, ∀ i : Fin (I.q (s + 1)),
        apVal I (s + 1) (cutset I cuts k (s + 1)) (rhs I s x i) ≤ Qo I s x i) ∧
      ∀ k, apVal I 1 (cutset I cuts k 1) I.b₁ ≤ Q₁ I := by sorry

end SDDPConv.Doasa
