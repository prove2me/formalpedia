-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_truncatedPureLoss
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.truncatedPureLoss
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:49:02.752308+00:00
-- url     : https://prove2.me/theorems/f3840e1d-321e-4660-ba39-2ad5a2f4d020
-- title:
--   Section V C: exact truncated pure-loss channel
-- statement:
--   Let $n\ge1$ and $0\le\eta\le1$. On $\mathcal H_n=\operatorname{span}\{|0\rangle,\ldots,|n-1\rangle\}$, define Kraus matrices $K_\ell$, $0\le\ell<n$, by
--
--   $$K_\ell|m\rangle=\begin{cases}\sqrt{\binom m\ell}(\sqrt{1-\eta})^{\ell}(\sqrt\eta)^{m-\ell}|m-\ell\rangle,&\ell\le m,\\0,&\ell>m.\end{cases}$$
--
--   The map $\mathcal L_{n,\eta}(X)=\sum_{\ell=0}^{n-1}K_\ell X K_\ell^\dagger$ is CPTP. If $\iota_n(X)=\sum_{i,j<n}X_{ij}|i\rangle\langle j|$ embeds the finite sector into the full oscillator space, then for every operator $X$ on $\mathcal H_n$,
--
--   $$\mathcal N[\eta,0](\iota_n(X))=\iota_n(\mathcal L_{n,\eta}(X)).$$
--
--   This is an exact invariant-subspace restriction of pure loss, including $\eta=0,1$, rather than a general thermal-channel truncation approximation.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 13, Section V C: exact truncated pure-loss channel

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- PDF p.13: exact invariant-sector pure-loss channel. At eta=0 every level
falls to vacuum; at eta=1 only ell=0 survives, with eta^0=1. -/
theorem truncatedPureLoss (n : ℕ) (hn : 0 < n) (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    IsChannel (truncatedLoss n eta) ∧
    ∀ X : Matrix (Fin n) (Fin n) ℂ,
      C.thermal eta 0 (embedTruncation X) = embedTruncation (truncatedLoss n eta X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
