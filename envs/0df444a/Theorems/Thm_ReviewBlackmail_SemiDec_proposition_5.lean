-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_proposition_5
-- name    : ReviewBlackmail.SemiDec.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:52.339102+00:00
-- url     : https://prove2.me/theorems/9b4272b3-22d6-4b12-ad18-e0828ee64593
-- title:
--   Proposition 5, p. 21 — under semi-decentralized dispute resolution the equilibrium ransom is π(a) − π(a^n_N) or (1 − δ)(γ(π(a) − π(a^d_N)) + b)
-- statement:
--   Consider the review-blackmail game under the semi-decentralized mechanism with timeliness $\gamma$, accuracy $\delta<1$ and penalty $b$, with genuine reviews kept, under the standing assumptions. Let
--   $$T:=\frac{1-\gamma(1-\delta)}{1-\delta}\big(\pi(a)-\pi(a^n_N)\big),\qquad \underline b:=(1-\gamma)\big[\pi(a)-\pi(a^s_N)\big].$$
--   The equilibrium ransom $r^*$ is the largest ransom at which settling is an equilibrium response and no other equilibrium response pays the seller more; the malicious consumer purchases iff such a ransom exceeds $p$.
--
--   1. If $b\ge T>\underline b$, then
--   $$r^*=\pi(a)-\pi(a^n_N),\tag{6}$$
--   and the malicious consumer purchases if and only if $p<\pi(a)-\pi(a^n_N)$.
--   2. If $\underline b\le b<T$, then
--   $$r^*=(1-\delta)\big(\gamma(\pi(a)-\pi(a^d_N))+b\big),\tag{7}$$
--   and the malicious consumer purchases if and only if $p<(1-\delta)\big(\gamma(\pi(a)-\pi(a^d_N))+b\big)$.
--
--   A high enough penalty makes the mechanism irrelevant to blackmail; below the threshold the ransom tracks the seller's expected loss from using the mechanism.
--
--   **Formalization Note** "$r^*$" is stated as `IsGreatest` of the set of ransoms at which settling prevails, never by its closed form. $\delta<1$ is added because the threshold divides by $1-\delta$ (at $\delta=1$ Lean's $x/0=0$ would place every $b$ in case 1). The conditions involving $\underline b$ are kept as printed; they come from Proposition 4, which justifies the game's restriction to sellers who keep genuine reviews ("By Proposition 4, under the assumption that $b\ge\underline b$, it suffices to focus on the strategies $ij=sn,dn,nn$", p. 41). Ransoms are not restricted to $r>0$; in both cases the greatest element is positive, so the restriction would not change it.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 21, Proposition 5, (6), (7)

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem proposition_5 (M : Model) (hM : M.Standing) (hδ : M.δ < 1) :
    ((1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) ≤ M.b →
      M.bLow < (1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) →
      IsGreatest {r | M.SettlePrevails r} (M.fut M.a - M.fut (M.post 1 1 .N)) ∧
        (M.Purchases ↔ M.p < M.fut M.a - M.fut (M.post 1 1 .N))) ∧
    (M.bLow ≤ M.b →
      M.b < (1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) →
      IsGreatest {r | M.SettlePrevails r}
          ((1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b)) ∧
        (M.Purchases ↔
          M.p < (1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b))) := by sorry
end ReviewBlackmail.SemiDec
