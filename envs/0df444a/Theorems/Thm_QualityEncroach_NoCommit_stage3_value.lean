-- Prove2me | Theorems.Thm_QualityEncroach_NoCommit_stage3_value
-- name    : QualityEncroach.NoCommit.stage3_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:28.202958+00:00
-- url     : https://prove2.me/theorems/7048de19-50eb-46f2-942b-5483a48539d0
-- title:
--   Proof of Proposition 7, p. 37 — stage-3 optimal q_M(τ,q_R,u_R) and the value functions Π^HF_M (τ ≥ 1), Π^LF_M (τ ≤ 1), equal at τ = 1
-- statement:
--   Consider the manufacturer's last move in the game without quality commitment. The wholesale price $w$, the retailer's quality $u_R>0$ and the retailer's order $q_R\ge0$ are given, and the manufacturer's direct-channel quality is written $u_M=\tau u_R$ with $\tau>0$. Let $\Pi_M(u_M,q_M)$ denote her profit $(w-ku_R^2)q_R + (p_M - c - ku_M^2)q_M$, with $k>0$, $c\ge0$.
--
--   1. If $\tau\ge1$ (direct product of higher quality), the quantity
--   $$
--   q_M(\tau,q_R,u_R) = \Big(\frac{-c-q_Ru_R-k\tau^2u_R^2+\tau u_R}{2\tau u_R}\Big)^{+}
--   $$
--   maximizes $\Pi_M(\tau u_R,\cdot)$ over $q_M\ge0$, and when it is positive the maximal profit equals
--   $$
--   \Pi^{HF}_M(\tau,q_R,u_R,w) = \frac{(c+u_R(q_R+\tau(k\tau u_R-1)))^2}{4\tau u_R} + q_R(w-ku_R^2).
--   $$
--   2. If $\tau\le1$ (direct product of lower quality), the quantity $\big((-c-\tau u_R(q_R+k\tau u_R-1))/(2\tau u_R)\big)^{+}$ maximizes $\Pi_M(\tau u_R,\cdot)$ over $q_M\ge0$, and when it is positive the maximal profit equals
--   $$
--   \Pi^{LF}_M(\tau,q_R,u_R,w) = \frac{(c+\tau u_R(q_R+k\tau u_R-1))^2}{4\tau u_R} + q_R(w-ku_R^2).
--   $$
--   3. $\Pi^{HF}_M(1,q_R,u_R,w) = \Pi^{LF}_M(1,q_R,u_R,w)$.
--
--   This reduces the manufacturer's stage-3 choice of quality to the one-variable problem of choosing $\tau$, which is the setting of the proof of Proposition 7.
--
--   **Formalization Note.** The paper displays only the $\tau\ge1$ quantity; the $\tau\le1$ quantity is its "similarly" counterpart. The profit identities are stated only when the optimal quantity is positive, since otherwise the optimal profit is $q_R(w-ku_R^2)$ rather than the squared formula.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 37, proof of Proposition 7 (q_M(τ,q_R,u_R), Π^HF_M, Π^LF_M)

import Mathlib
import Definitions.Def_QualityEncroach_NoCommit_Game

namespace QualityEncroach.NoCommit

/-- Proof of Proposition 7, p. 37: with the direct-channel quality written `u_M = τ u_R`
(`τ > 0`), the stage-3 quantity problem of the manufacturer is solved by `qMHF` for `τ ≥ 1`
and by `qMLF` for `τ ≤ 1`; when that quantity is positive the optimal profit is
`Π^HF_M` resp. `Π^LF_M`; and `Π^HF_M(1, ·) = Π^LF_M(1, ·)`. -/
theorem stage3_value (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR τ : ℝ)
    (huR : 0 < uR) (hqR : 0 ≤ qR) (hτ : 0 < τ) :
    (1 ≤ τ →
      (∀ qM : ℝ, 0 ≤ qM →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qM⟩ ≤
          mfrPayoff k c ⟨w, uR, qR, τ * uR, qMHF k c τ qR uR⟩) ∧
      (0 < qMHF k c τ qR uR →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qMHF k c τ qR uR⟩ = PiHF k c τ qR uR w)) ∧
    (τ ≤ 1 →
      (∀ qM : ℝ, 0 ≤ qM →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qM⟩ ≤
          mfrPayoff k c ⟨w, uR, qR, τ * uR, qMLF k c τ qR uR⟩) ∧
      (0 < qMLF k c τ qR uR →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qMLF k c τ qR uR⟩ = PiLF k c τ qR uR w)) ∧
    PiHF k c 1 qR uR w = PiLF k c 1 qR uR w := by sorry

end QualityEncroach.NoCommit
