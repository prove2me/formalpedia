-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_phiImprove_contraction
-- name    : WiesemannRMDP.SRect.phiImprove_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:35.53492+00:00
-- url     : https://prove2.me/theorems/b1592f56-e76e-4084-b190-5a9dd1c9a55d
-- title:
--   §4, proof of Theorem 4.1, p. 26 — the robust improvement map ϕ of (25) is a contraction
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions. The robust policy improvement map $\varphi:\mathbb R^S\to\mathbb R^S$,
--   $$\varphi_s(w) := \max_{\pi\in\Pi}\phi_s(\pi;w),\qquad s\in\mathcal S, \tag{25}$$
--   where $\phi$ is the robust evaluation map (11), is a contraction with respect to the maximum norm: there is $K<1$ with $\|\varphi(w)-\varphi(w')\|_\infty\le K\|w-w'\|_\infty$ for all $w,w'\in\mathbb R^S$.
--
--   By the Banach fixed point theorem $\varphi$ has a unique fixed point $w^*$, the optimal robust value of Theorem 4.1, which robust value iteration computes.
--
--   **Formalization Note.** In Lean, (25) is `phiImprove` and (11) is `phiEval`. Only the existence of a modulus $K<1$ is asserted, as in the paper. No rectangularity is assumed.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), §4, proof of Theorem 4.1, p. 26

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- §4, proof of Theorem 4.1, p. 26 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision
Processes*, Optimization Online 2610, revision of February 9, 2012): "One can adapt the results
in [12, 18] to show that ϕ is a contraction mapping."

The robust improvement map `ϕ` of (25), `ϕ_s(w) = max_{π∈Π} φ_s(π; w)`, is a contraction of
`ℝ^S` with some modulus `K < 1`.

**Formalization Note.** `ℝ^S` carries Mathlib's sup metric. The paper gives no modulus; only its
existence is asserted. No rectangularity is assumed. -/
theorem phiImprove_contraction {St Act : Type*} [Fintype St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing) :
    ∃ K : NNReal, K < 1 ∧ ContractingWith K M.phiImprove := by sorry

end WiesemannRMDP.SRect
