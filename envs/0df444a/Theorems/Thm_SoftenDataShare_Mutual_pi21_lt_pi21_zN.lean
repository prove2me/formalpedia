-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_pi21_lt_pi21_zN
-- name    : SoftenDataShare.Mutual.pi21_lt_pi21_zN
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:02.365977+00:00
-- url     : https://prove2.me/theorems/17714fc2-3c55-4374-bc5c-c6b0831d7c04
-- title:
--   Proof of Proposition 1, p. 35 — z^N is the unique maximizer of π₂₁(z) = (2z − 1)(1 − F(z)) on [0, 1]
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and let $z^N$ be the benchmark marginal consumer of Eq. (1). Write $\pi_{21}(z)=(2z-1)(1-F(z))$ for firm 2's profit when its uniform price $2z-1$ serves exactly the consumers in $[z,1]$. Then for every $z\in[0,1]$ with $z\neq z^N$,
--   $$\pi_{21}(z)<\pi_{21}(z^N).$$
--
--   In words, the benchmark price is firm 2's unique optimal uniform price: the first-order condition (1) identifies the global maximum. The proof of Proposition 1 uses this to compare firm 2's two pricing options after data sharing on $[z^N,b]$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 35, proof of Proposition 1; also p. 33, proof of Lemma 1, and footnote 14, p. 8

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem pi21_lt_pi21_zN {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, z ≠ zN → pi21 F z < pi21 F zN := by sorry

end SoftenDataShare.Mutual
