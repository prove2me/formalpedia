-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_eq_2_6
-- name    : SteutelVanHarn.SelfDec.eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:51:24.199991+00:00
-- url     : https://prove2.me/theorems/9bf6a749-b823-494a-af63-3f7f0bf4c4b5
-- title:
--   (2.6) — if $P$ is discrete self-dec, $\exp\{-r(1-z)P'(z)/P(z)\}$ is a p.g.f. for every $r>0$
-- statement:
--   Let $(p_n)$ be a discrete self-decomposable distribution on $\mathbb N_0$ with p.g.f. $P$ and $0<p_0<1$. Then for every $r>0$ the function
--   $$
--   Q_r(z)=\exp\{-r(1-z)P'(z)/P(z)\}\qquad(0\le z<1)
--   $$
--   is the p.g.f. of a distribution on $\mathbb N_0$: there is a distribution $(q_n)$ with $\sum_nq_nz^n=Q_r(z)$ for $0\le z<1$.
--
--   In the paper $Q_r$ arises as the limit of the p.g.f.'s $P_{\alpha_n}(z)^{r/(1-\alpha_n)}$ as $\alpha_n\uparrow1$; its being a p.g.f. for every $r>0$ shows that $Q=Q_1$ is infinitely divisible, which is the first half of the proof of Theorem 2.2.
--
--   **Formalization Note** $P'$ is Lean's `deriv` of `pgf p`; $P(z)>0$ on $[0,1)$ because $p_0>0$. The identity is required on $[0,1)$, which determines the p.g.f.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 3, proof of Theorem 2.2, (2.6) and the sentence following it

import Definitions.Def_SteutelVanHarn_SelfDec_SelfDec

namespace SteutelVanHarn.SelfDec

theorem eq_2_6 (p : ℕ → ℝ) (hp0 : 0 < p 0) (hp1 : p 0 < 1) (hsd : IsDiscreteSelfDec p) :
    ∀ r : ℝ, 0 < r → ∃ q : ℕ → ℝ, IsDistribution q ∧
      ∀ z ∈ Set.Ico (0 : ℝ) 1,
        pgf q z = Real.exp (-(r * (1 - z) * deriv (pgf p) z / pgf p z)) := by sorry

end SteutelVanHarn.SelfDec
