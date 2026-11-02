-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_renyi_shannon
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.renyi_shannon
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:19:40.365553+00:00
-- url     : https://prove2.me/theorems/b4596c37-a91a-43c8-a6fb-fa37479812a5
-- title:
--   §VII-C, unnumbered Renyi–Shannon comparison and limit
-- statement:
--   Let $p$ be a probability law on a finite nonempty alphabet. Define $H(p)=-\sum_xp(x)\log_2p(x)$, with $0\log_2 0=0$, and $H_{1+\alpha}(p)=-\alpha^{-1}\log_2\sum_xp(x)^{1+\alpha}$ for $\alpha>0$. Then
--   $$H_{1+\alpha}(p)\le H(p)\quad(0<\alpha\le1),\qquad \lim_{\alpha\downarrow0}H_{1+\alpha}(p)=H(p).$$
--
--   This is the ordinary finite Renyi--Shannon comparison and limit used in the leakage proof.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 16, §VII-C, unnumbered Renyi–Shannon comparison and limit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.16, (84): ordinary finite Renyi entropy is at most Shannon entropy
for 0<alpha≤1 and converges to it from positive alpha. -/
theorem renyi_shannon {A : Type*} [Fintype A] [Nonempty A]
    (p : A → ℝ) (hp : IsLaw p) :
    (∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → renyiBits p alpha ≤ observationEntropyBits p id) ∧
    Tendsto (fun alpha : ℝ => renyiBits p alpha) (nhdsWithin 0 (Ioi 0))
      (nhds (observationEntropyBits p id)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
