-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P03_explicitIntermediateAverage
-- name    : QAlgorithms.Papers.Independent.Gap48.P03.explicitIntermediateAverage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:01:33.634441+00:00
-- url     : https://prove2.me/theorems/c61de61f-4bf6-425a-834b-1d5c800b0156
-- title:
--   Explicit uniform phase-damping average for the intermediate channel
-- statement:
--   Let $d\ge2$ and $-1/(d-1)\le\lambda\le1$. Define $\Delta_\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I/d$ and $\Omega_\lambda(X)=\Delta_\lambda(X)+(1-\lambda)(X-\operatorname{diag}X)/d$. Let $G_{kk}=e^{2\pi i k/d}$ and $H_{kk}=e^{2\pi i k^2/(2d^2)}$ for $1\le k\le d$, with off-diagonal entries zero. Put $\theta=d^{-1/2}(1,\ldots,1)$, $u_{k,a}=G^kH^a\theta$, $E_{k,a}=|u_{k,a}\rangle\langle u_{k,a}|$, and $\Phi_\lambda^{(a)}(X)=\lambda X+(1-\lambda)\sum_k E_{k,a}XE_{k,a}$. For every $1\le a\le2d^2$ the constructed vectors form a uniform orthonormal basis and the corresponding map is CPTP. For every matrix $X$,
--
--   $$\Omega_\lambda(X)=\frac1{2d^2}\sum_{a=1}^{2d^2}\Phi_\lambda^{(a)}(X).$$
--
--   The identity describes the source’s concrete family, with its actual number of terms and its one-based phases.
-- source:
--   The capacity of the quantum depolarizing channel, arXiv:quant-ph/0204172v2, PDF p. 14, Lemma 11: explicit uniform phase-damping average for Ωλ

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

namespace QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0204172v2, PDF pp.13-16, Lemma 11, (54)-(57).
The concrete constructed columns are orthonormal and uniform; neither is assumed. -/
theorem explicitIntermediateAverage {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ) - 1) ≤ lam) (hhigh : lam ≤ 1) :
    (∀ a : Fin (2 * d^2),
      (constructedUniformBasis d (a.val + 1))ᴴ * constructedUniformBasis d (a.val + 1) = 1 ∧
      IsUniformBasis (constructedUniformBasis d (a.val + 1)) ∧
      IsChannel (constructedPhaseDamping d lam (a.val + 1))) ∧
    ∀ X : Matrix (Fin d) (Fin d) ℂ,
      intermediateChannel d lam X = (((2 * d^2 : ℕ) : ℂ)⁻¹) •
        ∑ a : Fin (2 * d^2), constructedPhaseDamping d lam (a.val + 1) X := by sorry

end QAlgorithms.Papers.Independent.Gap48.P03

end
