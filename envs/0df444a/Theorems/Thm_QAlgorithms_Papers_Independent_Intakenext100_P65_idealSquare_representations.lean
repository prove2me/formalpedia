-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_idealSquare_representations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.idealSquare_representations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:33:37.299521+00:00
-- url     : https://prove2.me/theorems/39eb9b9a-aeb1-4e75-8af8-41af921f225d
-- title:
--   Weak ideal square-code comb and coherent-lattice representations
-- statement:
--   For $\mu=0,1$, define the ideal position-comb functional on Schwartz functions by $T_\mu(f)=\sum_{n\in\mathbb Z}f(\sqrt\pi(2n+\mu))$. These sums converge absolutely, define continuous functionals, and $T_0,T_1$ are linearly independent. Translation by $2\sqrt\pi$ and multiplication by $e^{2i\sqrt\pi x}$ fix each functional. Let $q_n=\sqrt\pi(2n+\mu)$ and let $V_{\mu,r}(x)$ be the ordered coherent-lattice wave sum
--
--   $$\sum_{n,j\in\mathbb Z}e^{-r(n^2+j^2)}\pi^{-1/4}e^{-(x-q_n)^2/2}e^{i\sqrt\pi j(x-q_n)},\qquad r>0.$$
--
--   There is a single nonzero constant $c$ such that, for every logical label and every Schwartz test $f$,
--
--   $$\lim_{r\downarrow0}\int_{\mathbb R}V_{\mu,r}(x)f(x)\,dx=cT_\mu(f).$$
--
--   Each regularized pairing is integrable. This expresses nonzero weak combs and their stabilizer action, rather than a normalized ideal vector or bounded ideal projection.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 17, §VII (7.1)–(7.6), Appendix D2 (D5)–(D7): ideal square-code representations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.17--18,29 (7.1)--(7.6),(D5)--(D7): nonzero independent weak combs,
+1 stabilizers, and weak coherentCoordinates-lattice equivalence up to a NONZERO constant.
All limits are tested on Schwartz functions; no bounded ideal projector is asserted. -/
theorem idealSquare_representations :
    (∀ (mu : Fin 2) (f : SchwartzMap ℝ ℂ),
      Summable (fun n : ℤ => f (Real.sqrt Real.pi * (2 * (n : ℝ) + mu.val))) ∧
      Continuous (fun h : SchwartzMap ℝ ℂ => idealComb mu h) ∧
      idealComb mu (fun x => f (x + 2 * Real.sqrt Real.pi)) = idealComb mu f ∧
      idealComb mu (fun x => Complex.exp (Complex.I * (2 * Real.sqrt Real.pi * x)) * f x) =
        idealComb mu f) ∧
    (∀ a b : ℂ, (∀ f : SchwartzMap ℝ ℂ, a * idealComb 0 f + b * idealComb 1 f = 0) → a = 0 ∧ b = 0) ∧
    (∃ c : ℂ, c ≠ 0 ∧ ∀ (mu : Fin 2) (f : SchwartzMap ℝ ℂ),
      (∀ r > (0 : ℝ), Integrable (fun x : ℝ => regularizedLattice mu r x * f x)) ∧
      Tendsto (fun r : ℝ => ∫ x : ℝ, regularizedLattice mu r x * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c * idealComb mu f))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
