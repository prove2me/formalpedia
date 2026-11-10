-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_4_6
-- name    : RandTensorIso.Smoothed.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:14.467492+00:00
-- url     : https://prove2.me/theorems/528dfaa2-b506-4994-b011-6e9fe2e66365
-- title:
--   Lemma 4.6 (complex form, §4.4) — uniform minimum singular value bound
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution (on $\mathbb C$, §4.4). There is $c>0$, depending only on $K_\xi$, such that: let $p\le cn$, let $U\in\mathbb C^{d\times p}$ have orthonormal columns, and let $M\in\mathbb C^{n\times p}$ have independent rows $M_i=U^*X_i$, where each $X_i\in\mathbb C^d$ has i.i.d. entries $X_{ij}\sim\xi$. Then every deterministic $F\in\mathbb C^{n\times p}$ satisfies
--   $$\mathbb P\Big(\sigma_{\min}(F+M)<\tfrac14\sqrt n\Big)\le e^{-cn}.$$
--   For complex $\xi$ the paper replaces the Hanson–Wright step of the real proof by Bernstein's inequality and a net argument (§4.4).
--
--   **Formalization Note.** The law is that of $X=(X_{il})\in\mathbb C^{n\times d}$ with i.i.d. $\xi$ entries, and $M_{ik}=\sum_l\overline{U_{lk}}X_{il}$; orthonormal columns is $U^*U=I_p$.
--
--   Differences from the source:
--   - generalization: Lemma 4.6 for real ξ, U, F, X_i with M_i = U^⊤X_i → ξ on ℂ, complex U, F, X_i with M_i = U^*X_i, as §4.4 extends it; reason: §4.4 gives the complex proof; real data are a special case (U^* = U^⊤ for real U)
--   - reading: c > 0 depending only on K_ξ → c chosen from K before ξ, n, p, d, U, F and valid for every ξ with K_ξ = K; reason: the uniform reading of 'depending only on K_ξ'
--   - encoding: p ≤ cn with M an n × p matrix → 1 ≤ p ≤ cn; reason: σ_min of a matrix with no columns is undefined (Lean's placeholder value 0 would make the statement false)
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 52 (PDF 54), Lemma 4.6; p. 59 (PDF 61), §4.4 (complex case)

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open Matrix MeasureTheory

namespace RandTensorIso.Smoothed

/-- Lemma 4.6 (p. 52), complex form (§4.4, p. 59). For every `K > 0` there is `c > 0` (depending
only on `K_ξ = K`) such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℂ` with
`K_ξ = K`, all `1 ≤ p ≤ cn`, every `U ∈ ℂ^{d×p}` with orthonormal columns and every deterministic
`F ∈ ℂ^{n×p}`: if `M` has independent rows `M_i = U^* X_i`, where the `X_i ∈ ℂ^d` have i.i.d.
`ξ` entries, then `P(σ_min(F + M) < √n/4) ≤ e^{−cn}`. -/
theorem lemma_4_6 (K : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ξ : ProbabilityMeasure ℂ), IsStdSubGaussian (ξ : Measure ℂ) →
      subGaussConst (ξ : Measure ℂ) = K →
      ∀ (n p d : ℕ), 1 ≤ p → (p : ℝ) ≤ c * n →
      ∀ (U : Matrix (Fin d) (Fin p) ℂ), Uᴴ * U = 1 →
      ∀ (F : Matrix (Fin n) (Fin p) ℂ),
        matrixLaw ξ n d {X | sigmaMin (F + Matrix.of (fun i k => ∑ l, star (U l k) * X i l)) <
            Real.sqrt n / 4} ≤
          ENNReal.ofReal (Real.exp (-(c * n))) := by sorry

end RandTensorIso.Smoothed
