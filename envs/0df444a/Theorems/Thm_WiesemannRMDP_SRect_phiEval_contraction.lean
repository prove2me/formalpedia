-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_phiEval_contraction
-- name    : WiesemannRMDP.SRect.phiEval_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:38.795898+00:00
-- url     : https://prove2.me/theorems/b3836d69-8455-4887-bb4b-db620625ecc5
-- title:
--   §3.1, proof of Theorem 3.2, p. 16 — φ(π; ·) of (11) is a contraction with a unique fixed point
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions, and fix $\pi\in\Pi$. The robust policy evaluation map $\phi(\pi;\cdot):\mathbb R^S\to\mathbb R^S$,
--   $$\phi_s(\pi;w) := \min_{\xi\in\Xi}\Big\{\widehat r_s(\pi;\xi)+\lambda\sum_{s'}\widehat P_{ss'}(\pi;\xi)\,w_{s'}\Big\},\qquad s\in\mathcal S, \tag{11}$$
--   is a contraction with respect to the maximum norm: there is $K<1$ with $\|\phi(\pi;w)-\phi(\pi;w')\|_\infty\le K\|w-w'\|_\infty$ for all $w,w'$. Consequently $\phi(\pi;\cdot)$ has exactly one fixed point $w^*\in\mathbb R^S$.
--
--   The fixed point is the candidate optimal constant reward to-go of Theorem 3.2, and the contraction property justifies robust value iteration. No rectangularity is needed for this step.
--
--   **Formalization Note.** In Lean the map (11) is `phiEval`. Only the existence of a modulus $K<1$ is asserted, as in the paper.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), §3.1, proof of Theorem 3.2, p. 16

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- §3.1, proof of Theorem 3.2, p. 16 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision
Processes*, Optimization Online 2610, revision of February 9, 2012): "One can adapt the results
in [12, 18] to show that φ(π; ·) is a contraction mapping. Hence, the Banach fixed point theorem
guarantees existence and uniqueness of w∗ ∈ ℝ^S."

For every policy `π ∈ Π`, the robust evaluation map `φ(π; ·)` of (11) is a contraction of
`ℝ^S` (some modulus `K < 1`), and it has exactly one fixed point.

**Formalization Note.** `ℝ^S` carries Mathlib's sup metric, the `‖·‖_∞` of Corollary 3.3. The
paper gives no modulus; only its existence is asserted. No rectangularity is assumed: this step
holds for every ambiguity set of the form (3). -/
theorem phiEval_contraction {St Act : Type*} [Fintype St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) :
    (∃ K : NNReal, K < 1 ∧ ContractingWith K (M.phiEval π)) ∧
    ∃! w : St → ℝ, M.phiEval π w = w := by sorry

end WiesemannRMDP.SRect
