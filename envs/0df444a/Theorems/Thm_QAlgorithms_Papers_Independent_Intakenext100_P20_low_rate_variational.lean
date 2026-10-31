-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_low_rate_variational
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.low_rate_variational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:39:44.010549+00:00
-- url     : https://prove2.me/theorems/1e932713-eaf6-4bea-88a2-2a10c9afaa79
-- title:
--   Lemma 9 low-rate branch (A9), corrected (A20)–(A21)
-- statement:
--   Let $\rho$ be a normalized density matrix on a complex space of dimension $d>0$, with decreasing eigenvalues $a_1\ge\cdots\ge a_d\ge0$. Suppose the top eigenvalue has multiplicity $1\le k<d$, so $a_1=\cdots=a_k>a_{k+1}$. For $0\le R\le\log k$ set $v=-\log a_1-R$ and $\psi(s)=\log\operatorname{Tr}\rho^s$. Write $H$ for Shannon or von Neumann entropy in nats and $D$ for classical or quantum relative entropy, with value $+\infty$ on support violation. Then
--
--   $$\min_{H(b)=R}D(b\Vert a)=\min_{H(\sigma)=R}D(\sigma\Vert\rho)=\min_{H(b)\le R}D(b\Vert a)=\min_{H(\sigma)\le R}D(\sigma\Vert\rho)=v,$$
--   $$\min_{H(b)\ge R}D(b\Vert a)=\min_{H(\sigma)\ge R}D(\sigma\Vert\rho)=\max_{0<s\le1}\frac{(1-s)R-\psi(s)}s=0,$$
--   $$\sup_{s\ge1}\frac{(1-s)R-\psi(s)}s=v.$$
--
--   Here $b$ ranges over all probability vectors of length $d$, and $\sigma$ over all normalized density matrices on the same space. Every minimum and the displayed maximum is attained; the final supremum need not be. This gives the low-rate variational formulas without inverse-tilt or full-rank hypotheses.
--
--   **Source correction.** Equation (A20) prints $\log a_1-R$. Its missing minus is fixed by (A9) and the attaining-state calculation on PDF p.9; the correction was independently checked in moderation round 1; a fresh no-edit round is required after this round’s repairs.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 8, Lemma 9 low-rate branch (A9), corrected (A20)–(A21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 9, PDF pp.8-9, low-rate (A9), (A18)-(A21).
Correction: (A20) prints log a1-R; (A9) and the p.9 attaining-state calculation
uniquely give -log a1-R. No full-rank assumption or inverse tilt is used.
Every minimum is stated as an attained least value; the s>=1 expression is a supremum. -/
theorem low_rate_variational {d : ℕ} (hd : 0 < d)
    (rho : {M : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix M})
    (spectral : SpectralData rho.val) (k : ℕ) (hk : 0 < k) (hkd : k < d)
    (htop : ∀ i : Fin d, i.val < k → spectral.value i = spectral.value ⟨0, hd⟩)
    (hgap : spectral.value ⟨k, hkd⟩ < spectral.value ⟨0, hd⟩)
    (R : ℝ) (hR : 0 ≤ R) (hRk : R ≤ Real.log (k : ℝ)) :
    let a := spectral.value
    let value := ENNReal.ofReal (-Real.log (a ⟨0, hd⟩) - R)
    IsLeast (classicalDValues a (fun h => h = R)) value ∧
    IsLeast (quantumDValues rho (fun h => h = R)) value ∧
    IsLeast (classicalDValues a (fun h => h ≤ R)) value ∧
    IsLeast (quantumDValues rho (fun h => h ≤ R)) value ∧
    IsLeast (classicalDValues a (fun h => R ≤ h)) 0 ∧
    IsLeast (quantumDValues rho (fun h => R ≤ h)) 0 ∧
    IsGreatest {v : ℝ | ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      v = ((1 - s) * R - logPowerTrace rho.val s) / s} 0 ∧
    (⨆ s : {s : ℝ // 1 ≤ s},
      ENNReal.ofReal (((1 - s.val) * R - logPowerTrace rho.val s.val) / s.val)) = value := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
