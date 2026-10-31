-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_rationalCanonicalForm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.rationalCanonicalForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:32:28.88199+00:00
-- url     : https://prove2.me/theorems/99cc9405-01bd-4750-8d93-52b6cdbf456a
-- title:
--   Simultaneous rank-one canonical form and converse
-- statement:
--   Let $d\ge1$. Suppose that $P$ has simple spectrum and $Q=v\varphi$, with $\varphi(v)\ne0$, is in general position with $P$: $Q$ annihilates no eigenvector, and its range has a nonzero component along every eigenline. There is an invertible change of basis $C$ in which $P$ is the companion matrix with superdiagonal ones and last row $a$, $Q$ has only its last row $b$ nonzero, and $P-Q$ is the companion matrix with last row $a-b$. Moreover $b_d=\operatorname{Tr}Q\ne0$. Writing
--
--   $$a(t)=t^d-\sum_{i=1}^d a_i t^{i-1},\qquad b(t)=\sum_{i=1}^d b_i t^{i-1},$$
--
--   we have $\operatorname{char}_P=a(t)$ and $\operatorname{char}_{P-Q}=a(t)+b(t)$. Conversely, for matrices in this displayed form, if $b_d\ne0$ and $P$ has simple spectrum,
--
--   $$\text{general position}\ \Longleftrightarrow\ a(t),b(t)\text{ have no common root}\ \Longleftrightarrow\ a(t),a(t)+b(t)\text{ have no common root}.$$
--
--   This is a simultaneous algebraic normal form; no ODE nonresonance is assumed. The plus sign in the characteristic polynomial corrects the printed minus sign, as forced by the displayed matrix subtraction.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 26, §20: Proposition (Rational Canonical Form)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §20 rational canonical form, PDF pp.26–27: simultaneous forms and both
converse equivalences. The displayed matrix c_i=a_i−b_i forces
char(P−Q)=a(t)+b(t); the printed c(t)=a(t)−b(t) has the opposite sign.
No ODE nonresonance is assumed in this purely algebraic result. -/
theorem rationalCanonicalForm (d : ℕ) (hd : 0 < d) :
    (∀ (P Q : Matrix (Fin d) (Fin d) ℂ),
      (∃ (v : Fin d → ℂ) (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ),
        phi v ≠ 0 ∧ Q = linearRankOneMatrix v phi) →
      RankOneGeneralPosition P Q →
      ∃ (C : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ),
        C.det ≠ 0 ∧ C⁻¹ * P * C = companionMatrix a ∧
        C⁻¹ * Q * C = lastRowMatrix b ∧
        C⁻¹ * (P - Q) * C = companionMatrix (fun i => a i - b i) ∧
        b ⟨d - 1, by omega⟩ = Matrix.trace Q ∧ b ⟨d - 1, by omega⟩ ≠ 0 ∧
        P.charpoly = companionPolynomial a ∧
        (P - Q).charpoly = companionPolynomial a + rowPolynomial b) ∧
    (∀ (a b : Fin d → ℂ), b ⟨d - 1, by omega⟩ ≠ 0 →
      HasSimpleSpectrum (companionMatrix a) →
      (RankOneGeneralPosition (companionMatrix a) (lastRowMatrix b) ↔
        NoCommonRoot (companionPolynomial a) (rowPolynomial b)) ∧
      (NoCommonRoot (companionPolynomial a) (rowPolynomial b) ↔
        NoCommonRoot (companionPolynomial a) (companionPolynomial a + rowPolynomial b)) ∧
      (companionMatrix a - lastRowMatrix b).charpoly =
        companionPolynomial a + rowPolynomial b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
