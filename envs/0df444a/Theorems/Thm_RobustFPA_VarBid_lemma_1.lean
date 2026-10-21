-- Prove2me | Theorems.Thm_RobustFPA_VarBid_lemma_1
-- name    : RobustFPA.VarBid.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:37.084791+00:00
-- url     : https://prove2.me/theorems/41d01d6f-101b-4d88-9cd2-cf1624d086d7
-- title:
--   Lemma 1 (corrected) — maximal loss over $\mathcal B_{\tau,G}$ is the supremum over environments where all unconstrained bidders bid the same
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$, $0 \le L < v_1$, and let $G$ be uniform on $[L, v_1]$. For $x \ge L$ let $B_x \in \mathcal B_{\tau,G}$ be the environment in which every unconstrained opponent bids $x$. Then for every bid $b_1 \ge 0$,
--   $$
--   \sup_{B \in \mathcal B_{\tau,G}} l(b_1, B \mid v_1) = \sup_{x \ge L} l(b_1, B_x \mid v_1).
--   $$
--   The statement also records that each $B_x$, $x \ge L$, lies in $\mathcal B_{\tau,G}$.
--
--   This is the paper's "for any bid $b_1$ there is a worst-case bid distribution where all unconstrained bidders submit the same bid", with "worst case" read as the paper does on p. 11: a worst case may be a limit of environments ("marginally below $h$"). It reduces the maximal loss over an infinite-dimensional set to a one-parameter family.
--
--   **Formalization Note.** $\mathcal B_{\tau,G}$ is the corrected set of the AmbiguitySet file (unconstrained bids $\ge L$, independent of the constraint pattern); the printed set makes the lemma false for $n \ge 3$. The paper states Lemma 1 for a general $G$; here $G$ is uniform, the case of Proposition 4. The paper's standing assumptions $n \ge 2$, non-negative bids, and a probability $\tau$ are made explicit as $0 < \tau < 1$ and $0 \le L < v_1$ ($L < v_1$ is needed for $G$ to exist).
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 21, Lemma 1 (proof: Appendix B.3, p. 48); posed for the corrected B_{τ,G} and G uniform

import Mathlib
import Definitions.Def_RobustFPA_VarBid_Model
import Definitions.Def_RobustFPA_VarBid_AmbiguitySet

namespace RobustFPA.VarBid

theorem lemma_1 (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hL : 0 ≤ L) (hLv : L < v) (b : ℝ) (hb : 0 ≤ b) :
    (∀ x : ℝ, L ≤ x → commonBidEnv n τ (uniformG L v) x ∈ varBidSet n τ L (uniformG L v)) ∧
    maxLoss v b (varBidSet n τ L (uniformG L v)) =
      sSup ((fun x => loss v b (commonBidEnv n τ (uniformG L v) x)) '' Set.Ici L) := by sorry

end RobustFPA.VarBid
