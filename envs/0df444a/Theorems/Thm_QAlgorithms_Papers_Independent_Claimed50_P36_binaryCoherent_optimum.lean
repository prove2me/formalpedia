-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_binaryCoherent_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.binaryCoherent_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:34:59.10523+00:00
-- url     : https://prove2.me/theorems/565f0401-4131-443c-93f0-f626d8c9cc94
-- title:
--   Exact optimal binary coherent discretization and optimizer
-- statement:
--   Fix $m\ge0$. Optimize over two coherent letters $|\alpha\rangle,|\beta\rangle$ and their priors $Q,1-Q$, subject to $Q|\alpha|^2+(1-Q)|\beta|^2\le m$, with product codes and unrestricted collective decoding. Put $h(q)=-q\log q-(1-q)\log(1-q)$ in nats. The optimal binary capacity is
--
--   $$
--   C^{(2)}(m)=h\!\left(\frac{1-e^{-2m}}2\right).
--   $$
--
--   For every $\alpha$ with $|\alpha|^2=m$, the alphabet $\{|\alpha\rangle,|-\alpha\rangle\}$ attains this capacity. Its equal-prior mixture has entropy equal to the displayed value. The feasible rate sets are bounded above. At $m=0$ the letters coincide and the rate is zero.
--
--   This gives both the exact value and the symmetric optimizer, rather than a formula for one preselected binary alphabet.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 17, Eqs.(68)-(70)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF pp.16-17, Eqs.(68)-(70): exact binary coherent optimum and symmetric
optimizer. Every alpha with |alpha|²=m gives an optimal pair alpha,-alpha with
uniform prior. At m=0 the letters coincide and the value is zero. -/
theorem binaryCoherent_optimum (m : ℝ) (hm : 0 ≤ m) :
    BddAbove (binaryCollectiveRates m) ∧
    binaryCollectiveCapacity m = binaryValue m ∧
    ∀ alpha : ℂ, Complex.normSq alpha = m →
      BddAbove (fixedBinaryRates alpha (-alpha) m) ∧
      sSup (fixedBinaryRates alpha (-alpha) m) = binaryValue m ∧
      matrixEntropy (binaryMixtureGram alpha (-alpha) (1 / 2)) = binaryValue m := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
