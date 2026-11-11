-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_multi_direction_moment_encoding
-- name    : QuantumFunctionalEstimation.Master.multi_direction_moment_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:29:47.608208+00:00
-- url     : https://prove2.me/theorems/9e895630-f0bc-425f-85b8-20b5342c11ea
-- title:
--   Lemma 3.4 — Haar-random multi-direction moment encoding
-- statement:
--   Let $d\ge2$ and $d/6\le q\le d/3$ be integers, and set $r=d-q$. Let $\mu_0,\mu_1$ match moments zero through $L$, be supported on $[a,b]\subseteq[0,d/12]$, and have common mean $\nu\le1$. Let $P_b$ be the actual state laws from Definition 3.3 and let $\Omega_b^{(n)}=\int\rho^{\otimes n}\,dP_b(\rho)$ for an integer $n\ge1$. Put $M=\sup_{x\in[a,b]}|x-1|$ and $R=128nM^2/(25r^2)$. If $R<1$ and $a<b$, then
--   $$T(\Omega_0^{(n)},\Omega_1^{(n)})\le q\left(\sqrt{\frac{R^{L+1}}{1-R}}+\exp\left(-\frac d{96(b-a)^2}\right)\right).$$
--   When $a=b$, the distance is zero. The constructed state laws have total mass one in both cases.
--
--   This bound controls the exact multi-direction hard priors used by the master theorem, including their fallback to the maximally mixed state.
--
--   Differences from the source:
--   - reading: the exponential divides by (b-a)^2 even at zero width → distance zero when a=b, and the exact printed bound when a<b; reason: the laws coincide at zero width; d=12, q=3, n=L=1 and both laws delta_0 on [0,0] satisfy all hypotheses but the printed exponent is undefined
--   - encoding: two probability distributions constructed in Definition 3.3 → the explicitly defined state-space measures together with conclusions that each is a probability measure; reason: ensures that a failed pushforward or pullback cannot satisfy the result by a zero-measure default
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Lemma 3.4 and Definition 3.3, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Encodings
import Definitions.Def_QuantumFunctionalEstimation_Master_Functionals
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace QuantumFunctionalEstimation.Master

/-- Lemma 3.4, printed p.16 (PDF p.18). At zero width the laws coincide, giving T=0;
this completes the otherwise undefined printed exponential (d=12,q=3,I=[0,0] is an example). -/
theorem multi_direction_moment_encoding (d q L n : ℕ) (hd : 2 ≤ d)
    (hqlo : (d : ℝ) / 6 ≤ q) (hqhi : (q : ℝ) ≤ (d : ℝ) / 3)
    (hn : 1 ≤ n) (a b ν : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (d : ℝ) / 12)
    (μ₀ μ₁ : ProbabilityMeasure ℝ) (hmatch : MomentMatching L μ₀ μ₁)
    (hs₀ : Supported μ₀ (Set.Icc a b)) (hs₁ : Supported μ₁ (Set.Icc a b))
    (hmean₀ : (∫ x, x ∂(μ₀ : Measure ℝ)) = ν)
    (hmean₁ : (∫ x, x ∂(μ₁ : Measure ℝ)) = ν) (hν : ν ≤ 1) :
    let R : ℝ := 128 * n * radius a b ^ 2 / (25 * ((d - q : ℕ) : ℝ) ^ 2)
    let P₀ := multiPrior d q μ₀
    let P₁ := multiPrior d q μ₁
    let T := QAlgorithms.traceDistance (averageCopies P₀ n) (averageCopies P₁ n)
    IsProbabilityMeasure P₀ ∧ IsProbabilityMeasure P₁ ∧
      (R < 1 → if a = b then T = 0 else
        T ≤ q * (Real.sqrt (R ^ (L + 1) / (1 - R)) +
          Real.exp (-(d : ℝ) / (96 * (b - a) ^ 2)))) := by sorry

end QuantumFunctionalEstimation.Master
