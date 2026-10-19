-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_four_use_moment_certificate
-- name    : QAlgorithms.Papers.Independent.Information100.P56.four_use_moment_certificate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:27:23.685436+00:00
-- url     : https://prove2.me/theorems/ec060164-2375-429c-859b-bac17e197ca5
-- title:
--   Section VII D, Eq.(75): four-use noise is not a two-binomial mixture
-- statement:
--   Let $K$ have the exact weight distribution $(23089,33839,27248,11757,4067)/100000$ on $\{0,1,2,3,4\}$. Set $m_j=\mathbb E[\binom Kj]/\binom4j$ for $0\le j\le4$. Then
--
--   $$\det[m_{i+j}]_{i,j=0}^2>\frac{68}{1000000}>0.$$
--
--   There are no $a,\theta,\phi\in[0,1]$ representing this distribution as $a\operatorname{Bin}(4,\theta)+(1-a)\operatorname{Bin}(4,\phi)$. This is an exact rational nonrepresentation certificate, separate from numerical rate comparisons.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 20, Section VII D, Eq.(75): four-use noise is not a two-binomial mixture

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VII D, p.20, Eq.(75): exact rational moment certificate and the
nonrepresentation of that profile as a two-binomial mixture. -/
theorem four_use_moment_certificate :
    (68 : ℝ) / 1000000 <
      Matrix.det (fun i j : Fin 3 => factorialMoment (i.val + j.val)) ∧
    ¬ ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ theta ∈ Set.Icc (0 : ℝ) 1,
      ∃ phi ∈ Set.Icc (0 : ℝ) 1,
        ∀ k : Fin 5, fourWeight k = a * binomialFour theta k + (1 - a) * binomialFour phi k := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
