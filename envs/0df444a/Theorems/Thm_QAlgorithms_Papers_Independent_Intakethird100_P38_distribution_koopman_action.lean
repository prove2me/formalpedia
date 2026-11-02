-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_distribution_koopman_action
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.distribution_koopman_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:28:53.286137+00:00
-- url     : https://prove2.me/theorems/916a71aa-f3ff-42e9-ad63-7a0697a27465
-- title:
--   Distribution shifts induce a Koopman unitary group
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Let $\sigma\in\mathcal C$ and let $\mu$ be a probability law on the continuous real tempered dual with the characteristic functional in §1(d). Define the distribution shift by $(\theta_t\omega)(\psi)=\omega(\psi(\cdot+t))$. Then every $\theta_t$ preserves $\mu$, and there exists a group of complex unitaries $U(t)$ on the full $L^2(\mu)$ such that
--
--   $$U(0)=I,\qquad U(t+s)=U(t)U(s),\qquad (U(t)f)(\omega)=f(\theta_t\omega)\quad\mu\text{-almost everywhere}.$$
--
--   This defines the action through tests and almost-everywhere classes; it never assigns a point value to a tempered distribution.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 19, §8, unnumbered (8.4): distribution shift representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- §8, equation (8.4), PDF pp.18--19: the distribution shifts preserve the law and
induce a group of unitaries on full L2. Pullback equalities are almost everywhere.
This assertion does not use the false general Lemma 8.1 as a hypothesis. -/
theorem distribution_koopman_action (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ)
    (μ : Measure (Omega n)) (hμ : CharacteristicLaw σ μ) :
    ∃ U : KoopmanFamily μ, IsKoopman μ U := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
