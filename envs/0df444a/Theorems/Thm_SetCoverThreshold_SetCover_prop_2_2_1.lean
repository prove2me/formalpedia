-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_prop_2_2_1
-- name    : SetCoverThreshold.SetCover.prop_2_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:56:15.784536+00:00
-- url     : https://prove2.me/theorems/034b31fe-2e2c-4dc0-8d52-9a604f3f460b
-- title:
--   Proposition 2.2.1 — the clause–variable game has value $1-\varepsilon/3$
-- statement:
--   Let $\varphi$ be a 3CNF-5 formula with $M$ clauses, let $\tau^*$ be an assignment satisfying the largest number of clauses, and let $\varepsilon$ be the fraction of clauses $\tau^*$ leaves unsatisfied. Consider the one-round two-prover system: the verifier picks a clause uniformly at random and one of its three variables uniformly at random, sends the clause to the first prover and the variable to the second, and accepts when the first prover's three bits satisfy the clause and agree with the second prover's bit on the chosen variable. Then the optimal strategy of the provers is accepted with probability exactly
--
--   $$1-\frac{\varepsilon}{3}.$$
--
--   That is, some pair of strategies achieves $1-\varepsilon/3$, and no pair exceeds it. The proposition identifies the error of the base game whose parallel repetition Raz's theorem controls.
--
--   **Formalization Note** This is the game of `ProofSystem` with $\ell=1$; probabilities are uniform counts over the $3M$ random strings, and strategies are deterministic functions of the question. $\varepsilon$ is expressed through a maximizing assignment $\tau^*$ rather than a supremum.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 641, Proposition 2.2.1

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

theorem prop_2_2_1 (φ : Formula5) (τ : Fin φ.n → Bool)
    (hτ : ∀ τ' : Fin φ.n → Bool,
      (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ' (φ.var c p)))).card ≤
        (Finset.univ.filter (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card)
    (ε : ℝ)
    (hε : ε = 1 - ((Finset.univ.filter
      (fun c => φ.ClauseSatBy c (fun p => τ (φ.var c p)))).card : ℝ) / φ.M) :
    (∃ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ = 1 - ε / 3) ∧
      ∀ (P₁ : φ.Prover1Strategy 1) (P₂ : φ.Prover2Strategy 1),
        φ.twoProverAcceptFrac 1 P₁ P₂ ≤ 1 - ε / 3 := by sorry

end SetCoverThreshold.SetCover
