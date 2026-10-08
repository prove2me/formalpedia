-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_lemma_1_1
-- name    : SteutelVanHarn.SelfDec.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:25.732195+00:00
-- url     : https://prove2.me/theorems/a5737408-db5d-4a7a-8248-113a9f78b4cc
-- title:
--   Lemma 1.1 — $\lim_{x\uparrow1}(1-x)P'(x)=0$ for every p.g.f.
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P(z)=\sum_n p_nz^n$. Then
--   $$
--   \lim_{x\uparrow1}\,(1-x)\,P'(x)=0 .
--   $$
--   No moment assumption is made: $P'(1^-)$, the mean, may be infinite.
--
--   The lemma controls the behaviour of a p.g.f. at the boundary point $1$; in the proof of Theorem 2.2 it shows that $\exp\{-r(1-z)P'(z)/P(z)\}\to1$ as $z\uparrow1$.
--
--   **Formalization Note** $P'$ is Lean's `deriv` of the real function `pgf p`, which is the derivative of the power series on $(-1,1)$; the limit is taken along $x\to1$, $x<1$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 1, Lemma 1.1

import Definitions.Def_SteutelVanHarn_SelfDec_PGF

open Filter Topology

namespace SteutelVanHarn.SelfDec

theorem lemma_1_1 (p : ℕ → ℝ) (hp : IsDistribution p) :
    Tendsto (fun x : ℝ => (1 - x) * deriv (pgf p) x) (𝓝[<] 1) (𝓝 0) := by sorry

end SteutelVanHarn.SelfDec
