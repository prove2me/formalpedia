-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_correlated_hoeffding_limits
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.correlated_hoeffding_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:40:01.262991+00:00
-- url     : https://prove2.me/theorems/1fa08ce5-2dfb-4555-b8b6-9bcc619e5c7b
-- title:
--   Theorem III.3: scaled correlated-state Hoeffding limits (attributed to [6])
-- statement:
--   Let $\rho_n,\sigma_n$ be density operators on finite-dimensional complex Hilbert spaces $H_n$, which may vary with $n$. Let $c:\mathbb N\to\mathbb N$ be nondecreasing with $c(n)\to\infty$. Write $S_\alpha$ for the source's Petz relative entropy in bits, with powers taken only on supports. Assume $c(n)^{-1}(\alpha-1)S_\alpha(\rho_n\|\sigma_n)$ converges uniformly on $[0,1)$ to a real function $\psi$ differentiable on $(0,1)$. For $r>0$, let $\beta_{n,r}$ be the attained minimum of $\operatorname{Tr}(\sigma_n T)$ over effects $0\le T\le I$ satisfying $\operatorname{Tr}(\rho_n(I-T))\le2^{-c(n)r}$. Set
--
--   $$\overline H_r=\sup_{0\le\alpha<1}\left\{-\frac{\alpha r}{1-\alpha}+\frac{\psi(\alpha)}{\alpha-1}\right\}.$$
--
--   Both scaled limits exist and satisfy
--
--   $$\lim_{n\to\infty}\frac{\log_2\beta_{n,r}}{c(n)}=-\overline H_r,\qquad \lim_{n\to\infty}\frac{H_{c(n)r}(\rho_n\|\sigma_n)}{c(n)}=\overline H_r.$$
--
--   Here $H_s(\rho\|\sigma)=\sup_{0\le\alpha<1}\{-\alpha s/(1-\alpha)+S_\alpha(\rho\|\sigma)\}$. For every $0\le\alpha<1$, the mean Rényi limit exists and equals $\psi(\alpha)/(\alpha-1)$; consequently the local meanRenyi lower-limit definition has that same value. Limits and extrema are extended-real, with $\log_2(0)=-\infty$. The unused finite prefix at $n=0$ does not affect the limits. The source attributes this theorem to Hiai–Mosonyi–Ogawa [6].
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 5, Theorem III.3: correlated-state Hoeffding theorem (cited [6])

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Theorem III.3, PDF p.5, attributed there to Hiai–Mosonyi–Ogawa [6].
Both scaled limits exist, with the displayed Hoeffding transform. The finite-block
error is minimized over actual effects with alpha_n <= 2^(-c(n) r), with attainment.
The mean Renyi quantities are actual limits, not merely defined lower limits. -/
theorem correlated_hoeffding_limits {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (rho sigma : (n : ℕ) → Operator (J n))
    (hrho : ∀ n, IsDensityMatrix (rho n)) (hsigma : ∀ n, IsDensityMatrix (sigma n))
    (c : ℕ → ℕ) (hc : Monotone c) (hc_infty : Tendsto c atTop atTop)
    (psi : ℝ → ℝ) (huniform : UniformLogTraceLimit c rho sigma psi)
    (hdiff : DifferentiableOn ℝ psi (Ioo 0 1)) :
    let beta : ℕ → ℝ → EReal := fun n r =>
      ⨅ T : {T : Operator (J n) // IsEffect T ∧
        typeOneError (rho n) T ≤ (2 : ℝ) ^ (-(c n : ℝ) * r)},
        (typeTwoError (sigma n) T.1 : EReal)
    let H : ℝ → EReal := fun r => ⨆ a : {a : ℝ // 0 ≤ a ∧ a < 1},
      ((-a.1 * r / (1 - a.1) + psi a.1 / (a.1 - 1) : ℝ) : EReal)
    (∀ n : ℕ, 0 < n → ∀ r : ℝ, 0 < r →
      ReachesMinimum (fun T : {T : Operator (J n) // IsEffect T ∧
        typeOneError (rho n) T ≤ (2 : ℝ) ^ (-(c n : ℝ) * r)} =>
        (typeTwoError (sigma n) T.1 : EReal))) ∧
    (∀ a : ℝ, 0 ≤ a → a < 1 →
      Tendsto (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) *
        petzRelativeBits a (rho n) (sigma n)) atTop (𝓝 ((psi a / (a - 1) : ℝ) : EReal)) ∧
      meanRenyi c rho sigma a = ((psi a / (a - 1) : ℝ) : EReal)) ∧
    (∀ r : ℝ, 0 < r →
      Tendsto (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) * logBits (beta n r))
        atTop (𝓝 (-H r)) ∧
      Tendsto (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) *
        petzHoeffdingBits ((c n : ℝ) * r) (rho n) (sigma n)) atTop (𝓝 (H r))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
