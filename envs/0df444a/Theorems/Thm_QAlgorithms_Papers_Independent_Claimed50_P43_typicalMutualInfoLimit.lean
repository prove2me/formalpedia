-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_typicalMutualInfoLimit
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.typicalMutualInfoLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:20:29.028582+00:00
-- url     : https://prove2.me/theorems/df29ce75-7667-491d-86b7-7019e61f749f
-- title:
--   Iterated typical-projector mutual-information limit
-- statement:
--   Let $\rho$ be a normalized density operator on a nonzero finite-dimensional space $A$, and fix an orthonormal spectral basis with eigenvalues $\lambda_j\ge0$ summing to one. Let $\Phi:A\to A'$ be CPTP with nonzero finite output. For $n\ge1$ and $\delta>0$, retain words for which every empirical frequency differs from $\lambda_j$ by less than $\delta$, excluding every zero-eigenvalue symbol. Let $P_{n,\delta}$ project onto these tensor eigenvectors and put $\bar\rho_{n,\delta}=P_{n,\delta}/\operatorname{rank}P_{n,\delta}$ whenever the rank is positive. For every sufficiently small fixed $\delta>0$, that rank is eventually positive, the inner limit exists, and
--
--   $$\lim_{\delta\downarrow0}\lim_{n\to\infty}\frac1n I(\bar\rho_{n,\delta};\Phi^{\otimes n})=I(\rho;\Phi).$$
--
--   Entropy and mutual information are in bits; pure and singular inputs are included. The finite initial zero-rank extension is zero and is not called a state. This is an iterated limit, not a diagonal-sequence assertion.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 3, §II, equation (8): typical-input mutual-information limit

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.3, (8): genuine iterated limits, n first and then positive delta to zero.
Inner limit existence and eventual positive typical rank are conclusions for all
sufficiently small positive delta, as required by the source iterated limit. -/
theorem typicalMutualInfoLimit {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (hspec : IsSpectralData rho U lam)
    (N : Superop A C) (hN : IsChannel N) :
    ∃ L : ℝ → ℝ,
      (∀ᶠ delta : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < (typicalWords lam n delta).card) ∧
        Tendsto (fun n => inputMutualInfo (piSuperop (fun _ : Fin n => N))
          (typicalState U lam n delta) / n) atTop (nhds (L delta))) ∧
      Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds (inputMutualInfo N rho)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
