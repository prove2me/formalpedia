-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_proposition_4
-- name    : ReviewBlackmail.SemiDec.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:48.758007+00:00
-- url     : https://prove2.me/theorems/0ada3ebe-28aa-4e24-8dae-43e3267a5b26
-- title:
--   Proposition 4, p. 20 — the seller does not remove genuine negative reviews iff b ≥ b̲ = (1 − γ)[π(a) − π(a^s_N)]
-- statement:
--   Under the semi-decentralized mechanism let
--   $$\underline b:=(1-\gamma)\big[\pi(a)-\pi(a^s_N)\big].$$
--   Under the standing assumptions:
--
--   1. When the market believes that the seller settles with malicious consumers and keeps genuine negative reviews, removing a genuine negative review through the mechanism is not profitable for the seller, i.e. $(1-\gamma)\pi(a^s_0)+\gamma\pi(a^s_N)-b\le\pi(a^s_N)$, if and only if $b\ge\underline b$.
--   2. If moreover $0<\gamma<1$ and $b\ge\underline b$, then removing genuine negative reviews is not an equilibrium: when the market believes that the seller settles with malicious consumers and removes genuine negative reviews (posteriors $a^{sd}_R$ of (38)), keeping a genuine negative review is strictly more profitable, i.e.
--   $$\pi(a^{sd}_N)>(1-\gamma)\pi(a^{sd}_0)+\gamma\pi(a^{sd}_N)-b.$$
--
--   Together these say that the seller does not use the mechanism against genuine reviews exactly when the penalty is at least $\underline b$; this is why Proposition 5 restricts attention to $b\ge\underline b$ and to sellers who keep genuine reviews.
--
--   **Formalization Note** The statement follows the two claims into which the proof (pp. 40–41) splits Proposition 4, restricted, as the proof is, to the beliefs in which the malicious consumer settles or does not buy (the latter has the same posteriors). It is not a claim about every equilibrium of a larger game. The hypothesis $0<\gamma<1$ in part 2 is added: $\gamma>0$ makes $a^{sd}_N=a^s_N$ (at $\gamma=0$ no genuine negative review is ever visible), and at $\gamma=1$ one has $b=\underline b=0$ with removal a weak best response.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 20, Proposition 4; pp. 40–41, Proof of Proposition 4, (21); pp. 51–52, Proof of Proposition 13, (38)

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem proposition_4 (M : Model) (hM : M.Standing) :
    (M.KeepGenuineBR ↔ M.bLow ≤ M.b) ∧
    (0 < M.γ → M.γ < 1 → M.bLow ≤ M.b → ¬ M.RemoveGenuineBR) := by sorry
end ReviewBlackmail.SemiDec
