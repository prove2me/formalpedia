-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_entangling_cloner
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.entangling_cloner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:47:26.467055+00:00
-- url     : https://prove2.me/theorems/23c5320a-592b-4dea-ac83-a328b22eeae3
-- title:
--   §VII, (27)–(28): physical entangling-cloner realization
-- statement:
--   Let $\kappa>0$, $0<\eta<1$, $r\ge0$ and $\gamma\in\mathbb R$. Put $\delta=2(1-\eta)\sinh^2r$. Every prescribed finite $\delta\ge0$ admits such an $r\ge0$. Prepare Alice's coherent input and the normalized two-mode environmental squeezed vacuum with coefficients $(-e^{i\gamma}\tanh r)^n/\cosh r$ on $|n,n\rangle$. Apply the number-conserving beam splitter that sends $b^\dagger$ to $\sqrt\eta\,b^\dagger+\sqrt{1-\eta}\,e_1^\dagger$ and $e_1^\dagger$ to $-\sqrt{1-\eta}\,b^\dagger+\sqrt\eta\,e_1^\dagger$. Equivalently this is the source's angle satisfying $\sqrt\eta=\cos(\theta/2)$. The explicit binomial number-basis coefficients realize a vector $\Psi^\alpha_{BE_1E_2}$ on the full three-mode oscillator space and
--
--   $$\|\Psi^\alpha\|=1,\qquad \operatorname{Tr}_{E_1E_2}|\Psi^\alpha\rangle\langle\Psi^\alpha|=D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger.$$
--
--   Each matrix entry of the partial trace is a convergent sum. Eve retains both environment modes. The $r=0$ case is pure loss; the additive-noise endpoint $\eta=1,\delta>0$ is excluded from this finite-squeezing construction. The source's $R(\eta)$ in (27) is interpreted through its explicit angle relation in (28).
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 6, §VII, (27)–(28): physical entangling-cloner realization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.6, (27)--(28): physical finite-squeezing realization of Gaussian
noise. R(eta) in (27) means R(theta) with sqrt(eta)=cos(theta/2), resolved by
explicit number-basis action. eta=1 with delta>0 is not this realization. -/
theorem entangling_cloner (kappa eta r gamma : ℝ) (hk : 0 < kappa)
    (he : 0 < eta) (he1 : eta < 1) (hr : 0 ≤ r) :
    (∀ delta : ℝ, 0 ≤ delta → ∃ r0 : ℝ, 0 ≤ r0 ∧
      delta = 2 * (1 - eta) * Real.sinh r0 ^ 2) ∧
    let P : CoherentHeterodyneParameters := ⟨kappa, eta, 2 * (1 - eta) * Real.sinh r ^ 2,
      hk, he, he1.le, mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr he1.le)) (sq_nonneg _)⟩
    ∀ alpha : ℂ,
      (∀ z, clonerVector eta r gamma alpha z = clonerCoefficient eta r gamma alpha z) ∧
      ‖clonerVector eta r gamma alpha‖ = 1 ∧
      ∀ m n : ℕ,
        Summable (fun z : ℕ × ℕ => clonerVector eta r gamma alpha (m, z) *
          conj (clonerVector eta r gamma alpha (n, z))) ∧
        (∑' z : ℕ × ℕ, clonerVector eta r gamma alpha (m, z) *
          conj (clonerVector eta r gamma alpha (n, z))) =
          receivedState P alpha (fockKet n) m := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
