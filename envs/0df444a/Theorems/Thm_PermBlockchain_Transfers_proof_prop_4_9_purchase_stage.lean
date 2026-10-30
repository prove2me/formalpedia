-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proof_prop_4_9_purchase_stage
-- name    : PermBlockchain.Transfers.proof_prop_4_9_purchase_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:15:36.121979+00:00
-- url     : https://prove2.me/theorems/8f9fbf8f-f1c6-44ab-8453-e6eb59d93369
-- title:
--   Proof of Proposition 4.9: fee payers purchase from a manufacturer; non-payers take the outside option
-- statement:
--   In the setting of the fee-stage milestone, let $\phi^*\in\bigl(\frac{\Delta}{2}+L+h-\gamma,\ \Delta+L+h-\gamma\bigr]$. At the on-path history, for every consumer type:
--
--   1. a fee payer (who has learned every manufacturer's type) with $\phi_k\le\phi^*$ has a manufacturer $i$ with $u_{ik}\ge\phi_k$;
--   2. for a consumer who did not pay, with $\phi_k>\phi^*$, every manufacturer has $u_{ik}<\phi_k$.
--
--   With the rule that a consumer buys when her best utility (weakly) exceeds the outside option, all fee payers buy from a manufacturer and all non-payers take the outside option.
--
--   Differences from the source:
--   - generalization: φ* the threshold of Lemma B.1(b); standing m ≥ 2, 0 ≤ L, 0 ≤ l → every φ* in (Δ/2 + L + h − γ, Δ + L + h − γ]; 1 ≤ m, L and l arbitrary; reason: the paper's argument uses only this location of φ*; every instance is covered
--   - encoding: all the consumers that choose b_k = 1 will purchase from a manufacturer … that choose b_k = 0 will take the outside option → the utility inequalities that, with the tie rule of IsOptimalPurchase, force these choices; reason: the choice itself is part of the equilibrium; the milestone states the comparison the paper makes
--   - encoding: consumer beliefs and information under α = 1/2 (p. 9), with Bayes updating from the uniform prior on assignments with m of each type (p. 12) → every belief system satisfying IsConsistentBelief for paperStrategy, with the deterministic revelation `revealed`; reason: α = 1/2 signals carry no information, so the chain's exact revelation is the whole information structure; the statement holds for every consistent belief system
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered, p. 37 (PDF p. 38)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsConsistentBelief
import Definitions.Def_PermBlockchain_Transfers_utility
import Definitions.Def_PermBlockchain_Transfers_paperStrategy

namespace PermBlockchain.Transfers

/-- **Proof of Proposition 4.9: fee payers purchase from a manufacturer; non-payers take the outside option.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered, p. 37 (PDF p. 38): "Note that φ* ≤ ∆ + L + h − γ
according to the proof of Lemma B.1(b). When b_k = 1, we have that φ_k ≤ φ* ≤ ∆ + L + h − γ =
max_{i∈M} u_ik holds and thus all the consumers that choose b_k = 1 will purchase from a
manufacturer rather than taking the outside option. Similarly, when b_k = 0, we have that
φ_k > φ* > ∆/2 + L + h − γ = max_{i∈M} u_ik and thus all the consumers that choose b_k = 0 will
take the outside option."

At the on-path history of `paperStrategy γ h l` under a consistent belief system, with
`φ* ∈ (Δ/2 + L + h − γ, Δ + L + h − γ]` and `H = L + Δ`: (1) a fee payer with `φ ≤ φ*` has some
manufacturer with utility at least `φ`; (2) for a non-payer with `φ > φ*` every manufacturer's
utility is below `φ`. With the tie rule of `IsOptimalPurchase`, payers buy and non-payers take
the outside option.

**Formalization Note.** Only the location of `φ*` is used, not `h(φ*; φ*) = 0`. -/
theorem proof_prop_4_9_purchase_stage {m : ℕ} (hm : 1 ≤ m) {L Δ h l γ : ℝ} (hΔ : 0 < Δ)
    (hlh : l < h) (hγ : 0 < γ) (φs : ℝ) (hφs : φs ∈ Set.Ioc (Δ / 2 + L + h - γ) (Δ + L + h - γ))
    (β : BeliefSystem m) (hβ : IsConsistentBelief (paperStrategy γ h l) β)
    (θ : Mfr m → MType) (hθ : θ ∈ Assignments m) (t : Horiz) :
    (∀ φ : ℝ, φ ≤ φs → ∃ i, φ ≤ utility (L + Δ) L h l
        (β (histOf (onPath (paperStrategy γ h l) θ)) true
          (revealed true θ (histOf (onPath (paperStrategy γ h l) θ))))
        (histOf (onPath (paperStrategy γ h l) θ)) i t) ∧
      (∀ φ : ℝ, φs < φ → ∀ i, utility (L + Δ) L h l
        (β (histOf (onPath (paperStrategy γ h l) θ)) false noInfo)
        (histOf (onPath (paperStrategy γ h l) θ)) i t < φ) := by sorry

end PermBlockchain.Transfers
