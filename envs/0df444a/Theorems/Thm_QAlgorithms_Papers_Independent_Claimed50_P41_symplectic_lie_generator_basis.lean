-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_lie_generator_basis
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_lie_generator_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:03:28.80719+00:00
-- url     : https://prove2.me/theorems/3dfcdeb7-2d75-457d-9bf7-8acff9425d73
-- title:
--   §V (5.1)–(5.3): Lie-algebra basis and brackets
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. In the source convention $S=e^{-itJ}$, put $(X_{ab})_{cd}=i(\delta_{ad}\beta_{cb}+\delta_{bd}\beta_{ca})$.
--
--   $$
--   [X_{ab},X_{cd}]=i(\beta_{ac}X_{bd}+\beta_{bc}X_{ad}+\beta_{ad}X_{cb}+\beta_{bd}X_{ca}).
--   $$
--
--   The symmetric-index generators with a at most b form a real basis of all purely imaginary J with beta J and J beta symmetric. Its dimension is n(2n+1). Conversely each such J exponentiates to a real symplectic one-parameter group. The corresponding standard real Lie-algebra matrices are -iJ.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 19, §V (5.1)–(5.3): Lie-algebra basis and brackets

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.18–19, (5.1)–(5.3): imaginary generators, real Lie-algebra
parametrization, independent symmetric-index basis, dimension and all brackets.
This does not substitute a Lie-algebra count for the separate Lie-group dimension node. -/
theorem symplectic_lie_generator_basis (n : ℕ) (hn : 0 < n) :
    (∀ a b : Phase n, generatorMatrix a b = generatorMatrix b a ∧
      (∀ c d, star (generatorMatrix a b c d) = -generatorMatrix a b c d) ∧
      (complexify (sigma n) * generatorMatrix a b).IsSymm ∧
      (generatorMatrix a b * complexify (sigma n)).IsSymm) ∧
    LinearIndependent ℝ (fun p : {p : Phase n × Phase n // phaseNumber p.1 ≤ phaseNumber p.2} =>
      realGenerator p.val.1 p.val.2) ∧
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2))) = n * (2 * n + 1) ∧
    (∀ J : Matrix (Phase n) (Phase n) ℂ,
      ((∀ c d, star (J c d) = -J c d) ∧
        (complexify (sigma n) * J).IsSymm ∧ (J * complexify (sigma n)).IsSymm) ↔
      ∃ M ∈ Submodule.span ℝ (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2)),
        J = Complex.I • complexify M) ∧
    (∀ a b c d : Phase n, algebraCommutator (generatorMatrix a b) (generatorMatrix c d) =
      Complex.I • ((sigma n a c : ℂ) • generatorMatrix b d +
        (sigma n b c : ℂ) • generatorMatrix a d + (sigma n a d : ℂ) • generatorMatrix c b +
        (sigma n b d : ℂ) • generatorMatrix c a)) ∧
    (∀ J : Matrix (Phase n) (Phase n) ℂ,
      (∀ c d, star (J c d) = -J c d) →
      (complexify (sigma n) * J).IsSymm → (J * complexify (sigma n)).IsSymm →
      ∀ t : ℝ, let E := NormedSpace.exp ((-Complex.I * (t : ℂ)) • J)
        (∀ a b, (E a b).im = 0) ∧ PreservesCanonicalForm (fun a b => (E a b).re)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
