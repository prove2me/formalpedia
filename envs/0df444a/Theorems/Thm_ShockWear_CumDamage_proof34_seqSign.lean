-- Prove2me | Theorems.Thm_ShockWear_CumDamage_proof34_seqSign
-- name    : ShockWear.CumDamage.proof34_seqSign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:25.984095+00:00
-- url     : https://prove2.me/theorems/6e8ecfff-b09f-4a59-a60b-f5826d78330d
-- title:
--   Proof of (3.4), p. 633 — if $\bar P_k^{1/k}$ decreases, $\bar P_k - \zeta^k$ has at most one sign change, $+$ to $-$
-- statement:
--   Let $1 = \bar P_0 \ge \bar P_1 \ge \dots \ge 0$ and suppose $\bar P_k^{1/k}$ is decreasing in $k = 1, 2, \dots$. Then for every $\zeta$ with $0 \le \zeta \le 1$ the sequence
--   $$k \mapsto \bar P_k - \zeta^k, \qquad k = 0, 1, 2, \dots,$$
--   has at most one sign change, from $+$ to $-$ if one occurs: there are no $j < k$ with $\bar P_j - \zeta^j < 0 < \bar P_k - \zeta^k$.
--
--   This is the first step of the paper's proof of Theorem 3.1 (3.4): it is the input to the variation diminishing property of the Poisson kernel.
--
--   **Formalization Note** $\zeta^0 = 1$, so the $k = 0$ term is $\bar P_0 - 1 = 0$. The hypothesis $1 = \bar P_0 \ge \bar P_1 \ge \dots$ is the standing hypothesis of Theorem 3.1; $\bar P_k \ge 0$ is stated explicitly. $\bar P_k^{1/k}$ is a real power.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 633, proof of (3.4), first sentence

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem proof34_seqSign (P : ℕ → ℝ) (hP0 : P 0 = 1) (hanti : Antitone P)
    (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → SignPMSeq (fun k => P k - ζ ^ k) := by sorry

end ShockWear.CumDamage
