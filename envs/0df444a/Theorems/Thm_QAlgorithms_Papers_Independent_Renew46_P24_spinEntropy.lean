-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_spinEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.spinEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:40:52.54555+00:00
-- url     : https://prove2.me/theorems/ffde2cca-6f5e-4f90-a1a8-d3fde34fb462
-- title:
--   §2.1.4: spin magnetization microcanonical entropy
-- statement:
--   For $N$ spin-$1/2$ particles on $(\mathbb C^2)^{\otimes N}$, let $X_\alpha^N=N^{-1}\sum_{i=1}^N\sigma_i^\alpha$, where $\sigma^1,\sigma^2,\sigma^3$ are the Pauli matrices. Let $\mathbf m\in[-1,1]^3$ and put $m=\|\mathbf m\|_2$. Define $H^{\rm mc}(\mathbf m)$ as the supremum, over nonzero projection sequences concentrating at $\mathbf m$ under every continuous single-observable test, of $\limsup_N N^{-1}\log\operatorname{Tr}P^N$. Then
--
--   $$H^{\rm mc}(\mathbf m)=\begin{cases}-\dfrac{1-m}{2}\log\dfrac{1-m}{2}-\dfrac{1+m}{2}\log\dfrac{1+m}{2},&m\le1,\\-\infty,&m>1.\end{cases}$$
--
--   Logarithms are natural and $0\log0=0$. This gives $\log2$ at zero magnetization and zero at unit magnetization. The entropy identity is retained independently of the defective printed shell construction.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 6, §2.1.4: spin magnetization microcanonical entropy

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

/-- Spin entropy, PDF p.6: the explicit entropy formula, including minus infinity
outside the physical Bloch ball. This does not assume the faulty printed shell. -/
theorem spinEntropy (m : Fin 3 → ℝ) (hm : ∀ a, m a ∈ Set.Icc (-1) 1) :
    microcanonicalEntropy spinSystem m =
      if magnetizationLength m ≤ 1 then
        ((-((1 - magnetizationLength m) / 2) * Real.log ((1 - magnetizationLength m) / 2) -
          ((1 + magnetizationLength m) / 2) * Real.log ((1 + magnetizationLength m) / 2) : ℝ) : EReal)
      else ⊥ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
