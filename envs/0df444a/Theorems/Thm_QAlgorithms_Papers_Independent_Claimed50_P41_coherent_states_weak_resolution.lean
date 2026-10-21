-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_coherent_states_weak_resolution
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.coherent_states_weak_resolution
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:04:58.092227+00:00
-- url     : https://prove2.me/theorems/318b2289-06c2-4351-abdb-aee6bc51baec
-- title:
--   §VII (7.3)–(7.6): coherent states and resolution
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. For $z\in\mathbb C^n$ let $|z\rangle=D(\sqrt2\Re z,\sqrt2\Im z)|0\rangle$, where the vacuum is psi_(I,0), and put $d\mu(z)=\prod_r d^2z_r/\pi$. Here $|0\rangle(q)=\pi^{-n/4}e^{-q^Tq/2}$ and $|z\rangle=D(\sqrt2\Re z,\sqrt2\Im z)|0\rangle$.
--
--   $$
--   \langle z^\prime|z\rangle=e^{-\|z^\prime\|^2/2-\|z\|^2/2+z^{\prime\dagger}z}\ne0,\qquad\int |z\rangle\langle z|\,d\mu(z)=I\quad\text{weakly}.
--   $$
--
--   The whole coherent family exists in L2, every member has unit norm and a_r|z>=z_r|z>. The scalar weak integral is integrable for every pair of Hilbert vectors and yields their inner product, giving the weak coherent expansion. For every psi, exp(norm z squared/2) times the coefficient <conjugate z|psi> is entire analytic. The concrete displacement fixes the phase independently of any Fock-basis transport.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 26, §VII (7.3)–(7.6): coherent states and resolution

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.25–26, (7.3)–(7.6): concrete normalized coherent states,
annihilation eigenfunctions, exact nonzero overlaps, the weak resolution of
identity and the entire Bargmann coefficient. The infinite integral is scalar
weak operator integration, not an integral of operator norms. -/
theorem coherent_states_weak_resolution (n : ℕ) (hn : 0 < n) :
    ∃ coherent : (Fin n → ℂ) → Schrodinger n,
      (∀ z, (fun q => coherent z q) =ᵐ[volume] coherentWave z ∧ ‖coherent z‖ = 1) ∧
      (∀ (z : Fin n → ℂ) (r : Fin n) (q : Fin n → ℝ),
        annihilationFunction r (coherentWave z) q = z r * coherentWave z q) ∧
      (∀ zPrime z : Fin n → ℂ,
        inner (𝕜 := ℂ) (coherent zPrime) (coherent z) =
          Complex.exp (-(1 / 2 : ℂ) * ((∑ r, Complex.normSq (zPrime r) : ℝ) : ℂ) -
            (1 / 2 : ℂ) * ((∑ r, Complex.normSq (z r) : ℝ) : ℂ) +
              ∑ r, star (zPrime r) * z r) ∧
        inner (𝕜 := ℂ) (coherent zPrime) (coherent z) ≠ 0) ∧
      (∀ psi phi : Schrodinger n,
        Integrable (fun z => inner (𝕜 := ℂ) psi (coherent z) *
          inner (𝕜 := ℂ) (coherent z) phi) (multimodeCoherentMeasure n) ∧
        (∫ z, inner (𝕜 := ℂ) psi (coherent z) * inner (𝕜 := ℂ) (coherent z) phi
          ∂multimodeCoherentMeasure n) = inner (𝕜 := ℂ) psi phi) ∧
      (∀ psi : Schrodinger n, Differentiable ℂ (fun z : Fin n → ℂ =>
        Complex.exp ((1 / 2 : ℂ) * ((∑ r, Complex.normSq (z r) : ℝ) : ℂ)) *
          inner (𝕜 := ℂ) (coherent (fun r => star (z r))) psi)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
