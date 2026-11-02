-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_convolution_module
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.convolution_module
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:30:21.252478+00:00
-- url     : https://prove2.me/theorems/2627ecc2-a7b0-46ae-9637-1d4f3926a31c
-- title:
--   The convolution module property
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Let $\sigma\in\mathcal C$. Suppose a regular positive Borel measure $\tau$ belongs to $\mathcal C_b$: for each integer $p\ge1$ there are an integer $q\ge1$ and $C>0$, both independent of $v\in\mathbb R^n$, with
--
--   $$\int(1+|u+v|^2)^{-q}\,d\tau(u)\le C(1+|v|^2)^{-p}\qquad(\forall v\in\mathbb R^n).$$
--
--   Then $\sigma\star\tau\in\mathcal C$, where convolution is the pushforward of the product measure under addition. This is the module inclusion $\mathcal C\star\mathcal C_b\subset\mathcal C$ in every positive dimension.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 25, Theorem 11.1: the convolution module property

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 11.1, PDF pp.25--26: C is a convolution module over C_b.
In (11.1) both q and C are uniform in v; the proof's missing q is restored. -/
theorem convolution_module (n : ℕ) (hn : 0 < n)
    (σ τ : Measure (SpectralDomain n)) (hσ : InC σ) (hτ : InCb τ) :
    InC (measureConvolution σ τ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
