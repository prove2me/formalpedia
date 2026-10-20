-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_separable_stochastic_success
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.separable_stochastic_success
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:18:35.477061+00:00
-- url     : https://prove2.me/theorems/a5b09087-be57-45fd-bb36-93651fed7723
-- title:
--   Quantitative heralded SLOCC implementation
-- statement:
--   Let $N,m$ be positive integers, let the local dimensions $d_1,\ldots,d_N$ be positive, and set $D=\prod_k d_k$. Let $\mathcal J=(\mathcal E_1,\ldots,\mathcal E_m)$ be a separable instrument on this multipartite system. There exists a real success probability $p$ such that
--   $$
--   \frac1{mD^2}\le p\le1,\qquad
--   (p\mathcal E_1,\ldots,p\mathcal E_m,(1-p)\mathcal D)\in\mathrm{LOCC}_N,
--   $$
--   where $\mathcal D(\rho)=\operatorname{Tr}(\rho)I_D/D$ is completely depolarizing. The success flag is available, and $p$ is independent of the input state. LOCC permits local ancillary systems and disposal but supplies no entangled resource. This gives the source's explicit uniform probability and its proof's $N$-round implementation.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 8, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.8, Lemma 1 and its proof: the success bound and the claimed N-round implementation.
The asserted small product-Kraus representation in the proof is not a hypothesis. -/
theorem separable_stochastic_success {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (d : Fin N → ℕ) (hd : ∀ k, 0 < d k)
    (J : Fin m → Superop (Config d) (Config d)) (hJ : InSEP d J) :
    ∃ p : ℝ, 1 / ((m : ℝ) * (Fintype.card (Config d) : ℝ) ^ 2) ≤ p ∧
      p ≤ 1 ∧ 0 < p ∧ InRounds d N (stochasticInstrument p J) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
