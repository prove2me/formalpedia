-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_kacEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.kacEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:51:02.235991+00:00
-- url     : https://prove2.me/theorems/36cac011-b0dc-479e-9ab6-9f080eac2bcb
-- title:
--   §4.3: equality and explicit value of Kac-model ensemble entropies
-- statement:
--   For the Kac model on two $N$-qubit registers, use the scatterer Pauli-$z$ mean $X_0^N$ and the three spin Pauli means $X_\alpha^N$, each divided by the number of sites $N$. Let $x=(\mu,\mathbf m)\in[-1,1]^4$ and $m=\|\mathbf m\|_2$. Define $\eta(p)=-p\log p$ for $0<p\le1$, $\eta(0)=0$, and $\eta(p)=-\infty$ outside $[0,1]$. Then
--
--   $$H^{\rm mc}(x)=H_1^{\rm can}(x)=\eta\!\left(\frac{1+m}2\right)+\eta\!\left(\frac{1-m}2\right)+\eta\!\left(\frac{1+\mu}2\right)+\eta\!\left(\frac{1-\mu}2\right).$$
--
--   Both entropies use outer variational suprema over sequences and normalization by $N$, not by $2N$. The formula retains the nonphysical case $m>1$ through the $-\infty$ convention. It is an equilibrium entropy identity and needs no dynamical hypothesis or faulty shell-maximizer assumption.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 14, §4.3: equality and explicit value of Kac-model ensemble entropies

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14-15, (4.10): Kac microcanonical and mean-canonical entropies
coincide with the four eta terms per site, including nonphysical magnetizations. -/
theorem kacEntropy (mu : ℝ) (m : Fin 3 → ℝ)
    (hmu : mu ∈ Set.Icc (-1) 1) (hm : ∀ a, m a ∈ Set.Icc (-1) 1) :
    microcanonicalEntropy kacSystem (kacConfiguration mu m) =
      meanCanonicalEntropy kacSystem (kacConfiguration mu m) ∧
    meanCanonicalEntropy kacSystem (kacConfiguration mu m) =
      extendedEta ((1 + magnetizationLength m) / 2) +
      extendedEta ((1 - magnetizationLength m) / 2) +
      extendedEta ((1 + mu) / 2) + extendedEta ((1 - mu) / 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
