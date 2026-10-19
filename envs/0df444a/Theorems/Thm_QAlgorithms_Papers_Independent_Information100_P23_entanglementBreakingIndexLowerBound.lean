-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_entanglementBreakingIndexLowerBound
-- name    : QAlgorithms.Papers.Independent.Information100.P23.entanglementBreakingIndexLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:13:34.254272+00:00
-- url     : https://prove2.me/theorems/b3afa985-3bde-4eab-8bd5-462aec424b2e
-- title:
--   §6 unnumbered: composed Bloch data and EB-index lower bound
-- statement:
--   Let $d\ge1$, fix a normalized Bloch basis, and let $\Phi$ be CPTP, with computed affine data $(A,c)$. For $n\ge0$ define $c_n=\sum_{j=0}^{n-1}A^jc$, so $c_0=0$. For every positive $n$, the computed Bloch data of $\Phi^n$ are $(A^n,c_n)$. If $\|A\|_{\mathrm{op}}<1$, then for every positive $n$ also $c_n=(I-A)^{-1}(I-A^n)c$.
--
--   Take each minimum below over positive integers, with the minimum of the empty set equal to infinity. Define $n_{\mathrm{EB}}(\Phi)=\min\{n\ge1:\Phi^n\text{ is EB}\}$ and
--
--   $$\nu_2(A,c)=\min\left\{n\ge1:\|A^n\|_*^2+\frac{d(d-1)}2|c_n|^2\le(d-1)^2\right\},\quad\nu_{\mathrm{blind}}(A)=\min\{n\ge1:\|A^n\|_*\le d-1\}.$$
--
--   Then, as inequalities in $\mathbb N\cup\{\infty\}$,
--
--   $$\nu_{\mathrm{blind}}(A)\le\nu_2(A,c)\le n_{\mathrm{EB}}(\Phi).$$
--
--   The contraction assumption is used only for the inverse closed form. The bound applies to arbitrary CPTP maps, without assuming they are already EB.
--
--   **Formalization Note** The source leaves empty minima implicit; extended natural infima make the convention explicit, including channels with no finite EB iterate.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 4, §6 unnumbered: composed Bloch data and EB-index lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- PDF p.4, §6: affine iterates, the contractive inverse formula, and the EB-index
lower bound. Empty minima are infinity; weak domination replaces the separately deferred
universal strict-improvement claim. Phi itself is only assumed CPTP. -/
theorem entanglementBreakingIndexLowerBound {d : ℕ} (hd : 1 ≤ d) (B : BlochBasis d)
    (Phi : ChannelMap d) (hPhi : IsCPTP Phi) :
    let A := blochA B Phi
    let c := blochC B Phi
    (∀ n : ℕ, 1 ≤ n → blochA B (Phi ^ n) = A ^ n ∧
      blochC B (Phi ^ n) = iterateTranslation A c n) ∧
    (operatorNorm A < 1 → ∀ n : ℕ, 1 ≤ n →
      iterateTranslation A c n = ((1 - A)⁻¹ * (1 - A ^ n)).mulVec c) ∧
    blindCrossingIndex (d := d) A ≤ quadraticCrossingIndex (d := d) A c ∧
    quadraticCrossingIndex (d := d) A c ≤ entanglementBreakingIndex Phi := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
