-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proof_prop_4_9_fee_stage_values
-- name    : PermBlockchain.Transfers.proof_prop_4_9_fee_stage_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:12:41.5649+00:00
-- url     : https://prove2.me/theorems/6e83ca0a-f89d-4b05-b29f-292a8ec413ec
-- title:
--   Proof of Proposition 4.9: the fee-stage values $g(1)$ and $g(0)$ at the full-adoption profile
-- statement:
--   In the transfer game of Proposition 4.9, suppose every manufacturer adopts the blockchain, high-type manufacturers set $P_i=\Psi_i=\gamma$ and low-type manufacturers set $P_i=\Psi_i=\max\{\gamma-(h-l),0\}$. Let $H=L+\Delta$ with $\Delta>0$, $l<h$, $\gamma>0$, $m\ge1$, and let consumers' beliefs be Bayes-consistent with this profile. Then at the resulting public history, for every fee $\kappa$, every consumer type and every outside option $\phi_k$,
--   $$g(1,\phi_k)=\max\{\Delta+L+h-\gamma,\ \phi_k\}-\kappa,\qquad g(0,\phi_k)=\max\Bigl\{\frac{\Delta}{2}+L+h-\gamma,\ \phi_k\Bigr\}.$$
--
--   A fee payer learns every manufacturer's type and her best manufacturer gives $H+h-\gamma$; a non-payer infers vertical types from the two prices, which differ, but not horizontal types, so her best manufacturer gives $\frac{H+L}{2}+h-\gamma$. These two values are the input to Lemma B.1.
--
--   Differences from the source:
--   - generalization: κ = Σ_i χ_i / G(φ) → every real κ; reason: the computation does not use the value of κ; the paper's κ is one instance
--   - generalization: standing assumptions m ≥ 2, 0 ≤ L, 0 ≤ l → 1 ≤ m, L and l arbitrary reals; reason: the computation needs only one manufacturer of each type; every instance of the paper satisfies the weaker hypotheses
--   - encoding: consumer beliefs and information under α = 1/2 (p. 9), with Bayes updating from the uniform prior on assignments with m of each type (p. 12) → every belief system satisfying IsConsistentBelief for paperStrategy, with the deterministic revelation `revealed`; reason: α = 1/2 signals carry no information, so the chain's exact revelation is the whole information structure; the statement holds for every consistent belief system
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered displays, pp. 36–37 (PDF pp. 37–38)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsConsistentBelief
import Definitions.Def_PermBlockchain_Transfers_feeValue
import Definitions.Def_PermBlockchain_Transfers_paperStrategy

namespace PermBlockchain.Transfers

/-- **Proof of Proposition 4.9: the fee-stage values `g(1)` and `g(0)` at the full-adoption profile.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered displays, pp. 36–37 (PDF pp. 37–38):
"When b_k = 1 … max_{i∈M} u_ik = H + h − γ = ∆ + L + h − γ. Therefore,
g(1, φ_k; φ) = … = max{∆ + L + h − γ, φ_k} − Σ_{i:i∈M} χ_i / G(φ)." and "When b_k = 0 … the
consumers are able to distinguish the vertically differentiated type … but they cannot distinguish
the horizontally differentiated type … Accordingly, max_{i∈M} u_ik = (H+L)/2 + h − γ =
∆/2 + L + h − γ. Therefore, g(0, φ_k; φ) = … = max{∆/2 + L + h − γ, φ_k}."

At the profile `paperStrategy γ h l` (everyone adopts; high types price `γ`, low types
`max{γ − (h − l), 0}`), with `H = L + Δ`, every consistent belief system gives these two values at
the on-path history, for every fee `κ`, consumer type `t` and outside option `φ`.

**Formalization Note.** The paper substitutes `κ = Σχ_i / G(φ)`; the identity holds for every
`κ`. `1 ≤ m` guarantees a manufacturer of each type. -/
theorem proof_prop_4_9_fee_stage_values {m : ℕ} (hm : 1 ≤ m) {L Δ h l γ : ℝ} (hΔ : 0 < Δ)
    (hlh : l < h) (hγ : 0 < γ) (κ : ℝ) (β : BeliefSystem m)
    (hβ : IsConsistentBelief (paperStrategy γ h l) β) (θ : Mfr m → MType)
    (hθ : θ ∈ Assignments m) (t : Horiz) (φ : ℝ) :
    feeValue (L + Δ) L h l β κ (histOf (onPath (paperStrategy γ h l) θ)) t φ true =
        max (Δ + L + h - γ) φ - κ ∧
      feeValue (L + Δ) L h l β κ (histOf (onPath (paperStrategy γ h l) θ)) t φ false =
        max (Δ / 2 + L + h - γ) φ := by sorry

end PermBlockchain.Transfers
