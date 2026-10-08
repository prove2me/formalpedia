-- Prove2me | Theorems.Thm_SDDPConv_Doasa_lemma2
-- name    : SDDPConv.Doasa.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:30:32.856412+00:00
-- url     : https://prove2.me/theorems/e79587c3-d8b5-47fc-b877-e7048d2bb880
-- title:
--   Lemma 2 — DOASA-N stops changing after finitely many iterations, with limiting value at most Q_1
-- statement:
--   Fix an instance satisfying (A4) and valid initial cuts. Consider DOASA-N with a fixed list of $N$ scenarios and arbitrary backward samples $\Omega^k_{s,t}$. Then in every realization there is an iteration $K$ after which the cut sets of all stages no longer change; consequently the forward solutions, the induced policy and the values $C^k_1$ are constant from $K$ on, and
--
--   $$\lim_k C^k_1\;=\;C^K_1\;\le\;Q_1 .$$
--
--   This is the deterministic half of the convergence proof: finiteness of the cut collection (Lemma 1) forces termination, whatever the sampling.
--
--   **Formalization Note** "Converges in a finite number of iterations to a policy" is stated as eventual constancy of the cut sets, which determines the forward solutions and the policy through the oracle. No probability enters. The lower bound needs the valid initial cuts.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 10, Lemma 2

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run

namespace SDDPConv.Doasa

/-- Lemma 2, p. 10: in every realization, DOASA-N stops changing its cuts (hence its forward
solutions and its policy) after finitely many iterations, and the limiting value `C^K_1` of
[AP_1] is at most the optimal value `Q_1` of [LP1]. -/
theorem lemma2 (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (hL : ValidInit I L) (sol : Oracle I)
    (Ls : List (Scen I)) (bw : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t))
    (hrun : IsDOASANRun I L sol Ls bw cuts D) :
    ∃ K, (∀ k, K ≤ k → ∀ t, cutset I cuts k t = cutset I cuts K t) ∧
      apVal I 1 (cutset I cuts K 1) I.b₁ ≤ Q₁ I := by sorry

end SDDPConv.Doasa
