-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_converse_P_alpha
-- name    : SteutelVanHarn.SelfDec.converse_P_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:51:11.392081+00:00
-- url     : https://prove2.me/theorems/65a214fa-420a-42f5-a79e-5493811ee152
-- title:
--   p. 4 — if $P$ is inf div with nonincreasing $r_n$, then $P_\alpha(z)=P(z)/P(1-\alpha+\alpha z)$ is an inf div p.g.f.
-- statement:
--   Let $(p_n)$ be an infinitely divisible distribution on $\mathbb N_0$ with p.g.f. $P$ and $0<p_0<1$, whose canonical sequence $(r_n)$ (defined by $(n+1)p_{n+1}=\sum_{k=0}^np_kr_{n-k}$) is nonincreasing. Then for every $\alpha\in(0,1)$ the function
--   $$
--   P_\alpha(z)=\frac{P(z)}{P(1-\alpha+\alpha z)}\qquad(0\le z\le1)
--   $$
--   is the p.g.f. of an infinitely divisible distribution on $\mathbb N_0$. In particular $P$ satisfies (2.1), so $(p_n)$ is discrete self-decomposable.
--
--   This is the converse half of Theorem 2.2.
--
--   **Formalization Note** $P(1-\alpha+\alpha z)>0$ for $z\in[0,1]$ because $p_0>0$, so the quotient is well defined. The identity is required on $[0,1]$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), pp. 3–4, proof of Theorem 2.2 (the converse direction, display of P_α and R_α)

import Definitions.Def_SteutelVanHarn_SelfDec_SelfDec

namespace SteutelVanHarn.SelfDec

theorem converse_P_alpha (p : ℕ → ℝ) (hp0 : 0 < p 0) (hp1 : p 0 < 1)
    (hinf : IsInfDiv p) (hr : Antitone (canonicalSeq p)) :
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ q : ℕ → ℝ, IsInfDiv q ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, pgf q z = pgf p z / pgf p (1 - α + α * z) := by sorry

end SteutelVanHarn.SelfDec
