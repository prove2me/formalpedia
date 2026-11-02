-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_schwartz_dense
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.schwartz_dense
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:25:29.599256+00:00
-- url     : https://prove2.me/theorems/b6c75138-0282-4e27-8a5e-d317a53ae087
-- title:
--   Schwartz functions are dense in spectral L2
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   For every $\sigma\in\mathcal C$, all $\psi\in\mathcal S$ belong to $L^2(\sigma)$, and their direct images, without Fourier transformation, are dense:
--
--   $$\overline{\{[\psi]_\sigma:\psi\in\mathcal S\}}^{\,L^2(\sigma)}=L^2(\sigma).$$
--
--   This density statement includes zero measures and finitely supported measures; it requires no infinite-dimensional hypothesis.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 10, Lemma 3.5: Schwartz density

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Lemma 3.5, PDF p.10: density of direct Schwartz inclusion, not its Fourier
transform. No infinite-dimensional assumption; zero and atomic measures are included. -/
theorem schwartz_dense (n : ℕ) (hn : 0 < n) (σ : Measure (SpectralDomain n)) (hσ : InC σ) :
    (∀ ψ : ComplexTest n, MemLp (fun x => ψ x) 2 σ) ∧
    DenseRange (fun ψ : ComplexTest n => l2Class σ ψ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
