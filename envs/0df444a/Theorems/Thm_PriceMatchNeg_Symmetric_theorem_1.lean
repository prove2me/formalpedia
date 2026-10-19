-- Prove2me | Theorems.Thm_PriceMatchNeg_Symmetric_theorem_1
-- name    : PriceMatchNeg.Symmetric.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:13.911978+00:00
-- url     : https://prove2.me/theorems/c98dbe1c-8485-415d-af0e-ccc71bb5cf82
-- title:
--   Theorem 1, p. 10 (PDF 10) — with symmetric power, the seller prefers PM to SN and both buyers prefer SN to PM
-- statement:
--   **Theorem 1 (Firms' preferences between PM and SN).** Let $a > 0$ be the demand base, $\gamma \in [0,1)$ the substitutability, and let both buyers have the same bargaining power $\theta \in (0,1)$ against the seller.
--
--   1. An equilibrium $(w_1, w_2) \in [0,a]^2$ of simultaneous negotiation exists, and an equilibrium wholesale price $w \in [0,a]$ of price-matching negotiation exists.
--   2. For every SN equilibrium $(w_1, w_2)$ and every PM equilibrium price $w$,
--   $$\pi_s(w_1, w_2) < \pi_s(w, w), \qquad \pi_1(w, w) < \pi_1(w_1, w_2), \qquad \pi_2(w,w) < \pi_2(w_2, w_1).$$
--
--   That is, the seller strictly prefers price matching to simultaneous negotiation, whereas both buyers strictly prefer simultaneous negotiation. Here $\pi_s$ and $\pi_i$ are the second-stage equilibrium profits of the seller and Buyer $i$; under PM the matched price $w$ applies to both buyers.
--
--   The result says that the preference split between the seller and the buyers is caused by the negotiation mechanism alone, not by any asymmetry between the buyers.
--
--   **Formalization Note** "Prefers" is read strictly; the paper's equality cases $\theta \in \{0, 1\}$ are excluded by $\theta \in (0,1)$. The sign $a > 0$ and the domain $[0,a]$ of equilibrium prices are added (see the Model definition). In PM the seller negotiates first with Buyer $1$; with symmetric power the choice of first buyer is immaterial. The conclusion is stated for every equilibrium of each mechanism, with existence, not for the closed-form prices.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), p. 10 (PDF 10), Theorem 1; proof: Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

theorem theorem_1 (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    (∃ w1 w2, IsSNEq P θ θ w1 w2) ∧ (∃ w, IsPMPrice P θ θ w) ∧
    ∀ w1 w2 w, IsSNEq P θ θ w1 w2 → IsPMPrice P θ θ w →
      piS P w1 w2 < piS P w w ∧ piB P w w < piB P w1 w2 ∧ piB P w w < piB P w2 w1 := by sorry

end PriceMatchNeg.Symmetric
