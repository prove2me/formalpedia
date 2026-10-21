-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_typicalOutputEntropyLimit
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.typicalOutputEntropyLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:21:26.218519+00:00
-- url     : https://prove2.me/theorems/60f0594a-6ba3-49e4-8957-da88e59ee922
-- title:
--   Iterated output-entropy limit of uniform typical subspaces
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional space $A$ and choose an orthonormal eigenbasis with nonnegative eigenvalues $\lambda_j$ summing to one. For $n\ge1$ and $\delta>0$, let $P_{n,\delta}$ be the projection onto tensor eigenvectors whose empirical frequencies differ from $\lambda_j$ by less than $\delta$, with zero-eigenvalue symbols excluded. Let $\Psi:A\to\widetilde A$ be any CPTP channel with nonzero finite output. Each sufficiently small fixed positive $\delta$ gives eventually positive typical rank and an existing inner limit, and
--
--   $$\lim_{\delta\downarrow0}\lim_{n\to\infty}\frac1n H\!\left(\Psi^{\otimes n}\!\left(\frac{P_{n,\delta}}{\operatorname{rank}P_{n,\delta}}\right)\right)=H(\Psi(\rho)).$$
--
--   All entropies are in bits, including the continuous zero-eigenvalue convention. No full-rank hypothesis is imposed on the input or output. The normalized projector's zero-rank extension affects only finitely many initial block lengths at fixed $\delta$. This is the channel-output continuity property used in the BSST proof.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 4, §II, equation (12): channel-output entropy of a normalized typical projector

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF pp.4--5, (12): arbitrary CPTP output; no full-rank input or output assumption.
The zero-rank total extension is used only before the eventual positive-rank tail.
Inner convergence is asserted for sufficiently small positive delta. -/
theorem typicalOutputEntropyLimit {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (hspec : IsSpectralData rho U lam)
    (N : Superop A C) (hN : IsChannel N) :
    ∃ L : ℝ → ℝ,
      (∀ᶠ delta : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < (typicalWords lam n delta).card) ∧
        Tendsto (fun n => vnEntropy (piSuperop (fun _ : Fin n => N)
          (typicalState U lam n delta)) / n) atTop (nhds (L delta))) ∧
      Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds (vnEntropy (N rho))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
