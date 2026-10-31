-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_strictInteger_geometricFamily
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.strictInteger_geometricFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:01:09.11605+00:00
-- url     : https://prove2.me/theorems/9ed82e70-e3fa-4eca-854a-aa4a87a34882
-- title:
--   Strict integer-scale geometric family
-- statement:
--   Let $\hbar>0$, let $v>0$ be the Gaussian displacement variance per real coordinate, and let $\lambda\ge1$ be an integer with $\lambda<\hbar/(ev)$. One can choose a single $\varepsilon>0$ with $c=e\lambda(v+\varepsilon)/\hbar<1$ and symplectic row matrices $S_N$ for every $N\ge1$. Define
--
--   $$
--   \Lambda_N=L\left(\sqrt{2\pi\hbar/\lambda}\,S_N\right),\quad \Delta_N=(2\pi\hbar/\lambda)^N,\quad a_N=\sqrt{2N(v+\varepsilon)}.
--   $$
--
--   These lattices have covolume $\Delta_N$ and geometric decoding failures $p_N$ satisfying
--
--   $$
--   p_N\le\Pr\{\|\xi_N\|>a_N\}+c^N,\qquad\Pr\{\|\xi_N\|>a_N\}\longrightarrow0,\qquad p_N\longrightarrow0.
--   $$
--
--   Here $\xi_N$ has $2N$ independent $N(0,v)$ coordinates. The dimensionless lattice $L(\sqrt\lambda S_N)$ has dual quotient of size $\lambda^{2N}$, hence algebraic multiplicity $\lambda^N$. No normalized physical encoder or decoder is asserted. At $\hbar/(ev)=k\ge2$ an integer, this result permits only $\lambda\le k-1$.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 6, §V, (64)–(68): strict integer-scale geometric asymptotic family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF pp.6–7, (64)–(68): strict integer-scale geometric family, with one epsilon
chosen before all N. The omitted tail is restored, and tends to zero. There is
no endpoint extension and no assertion about normalized physical quantum codes. -/
theorem strictInteger_geometricFamily (hbar : ℝ) (hhbar : 0 < hbar)
    (v : NNReal) (hv : 0 < v) (lambda : ℕ) (hlambda : 1 ≤ lambda)
    (hstrict : (lambda : ℝ) < hbar / (Real.exp 1 * (v : ℝ))) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      Real.exp 1 * (lambda : ℝ) * ((v : ℝ) + epsilon) / hbar < 1 ∧
      ∃ S : (N : ℕ) → Generator N,
        (∀ N, 1 ≤ N →
          IsSymplectic (S N).transpose ∧ (S N).det ≠ 0 ∧
          Nat.card (DualCosets (Real.sqrt (lambda : ℝ) • S N)) = lambda ^ (2 * N) ∧
          |(physicalNormalizer hbar lambda (S N)).det| =
            (2 * Real.pi * hbar / (lambda : ℝ)) ^ N ∧
          decodingFailure (physicalNormalizer hbar lambda (S N)) v ≤
            displacementTail N v (Real.sqrt (2 * (N : ℝ) * ((v : ℝ) + epsilon))) +
              (Real.exp 1 * (lambda : ℝ) * ((v : ℝ) + epsilon) / hbar) ^ N) ∧
        Filter.Tendsto (fun N =>
          displacementTail N v (Real.sqrt (2 * (N : ℝ) * ((v : ℝ) + epsilon))))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun N => decodingFailure (physicalNormalizer hbar lambda (S N)) v)
          Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
