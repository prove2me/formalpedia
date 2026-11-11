-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_7_1
-- name    : SampQueryLB.WarmSLC.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:21.779176+00:00
-- url     : https://prove2.me/theorems/650922d0-8338-4a58-b353-c7b794fa50a2
-- title:
--   Lemma 7.1 — properties of the warm initialization: smooth positive even density, mean zero, $d\nu/d\pi\le3$, $d\pi/d\nu\le100$, slab bounds $3/100$ and $a_b>0.206$
-- statement:
--   For an admissible $\vartheta$, $\Xi\in E_n$ and a unit vector $v\in S^{n-1}$, let $\nu_{\Xi,v}(dx)\propto f(v^\top x_h)\pi^\Xi(dx)$ with $f=\frac1{100}+\frac{99}{100}\vartheta$ and normalizer $Z^{\mathrm{init}}_{\Xi,v}$ (§7.1).
--
--   **Lemma 7.1.** For every $\Xi\in E_n$ and $v\in S^{n-1}$, $\nu_{\Xi,v}$ has a smooth, everywhere positive, even density, a finite first moment, and mean zero. Its normalizer and density ratios satisfy
--   $$1-\frac1{\sqrt\pi}\le Z^{\mathrm{init}}_{\Xi,v}\le1,\qquad\frac{d\nu_{\Xi,v}}{d\pi^\Xi}\le3,\qquad\frac{d\pi^\Xi}{d\nu_{\Xi,v}}\le100.$$
--   For $b=\frac7{25}$ and $a_b=\frac{2be^{-b^2}}{\sqrt{2\pi}}>0.206$,
--   $$\nu_{\Xi,v}\big(|v^\top x_h|\le\tfrac9{20}\big)\le\tfrac3{100},\qquad\pi^\Xi\big(|v^\top x_h|\le b\big)\ge a_b.$$
--
--   The initialization is a constant-warm start that is biased away from a central slab of the hidden direction $v$, which the algorithm never sees.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. "Smooth" is $C^\infty$ (`ContDiff ℝ ∞`); the density is with respect to Lebesgue measure; a finite first moment and mean zero are `MeanZero` (the identity is Bochner integrable with integral $0$); the ratio bounds are absolute continuity with Radon–Nikodym derivatives bounded almost everywhere (`RatioBounds`); the numerical claim $a_b>0.206$ is a conjunct.
--
--   Differences from the source:
--   - reading: 'Fix an even function ϑ ∈ C^∞(R; [0,1]) equal to zero for |t| ≤ 9/20 and to one for |t| ≥ 1/2' (§7.1) → ∀ ϑ with IsSlabProfile ϑ, quantified before the constants; reason: the construction fixes an arbitrary such ϑ first; the statement holds for each of them
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: v ∈ S^{n−1}; v^⊤x_h → v : Point n with ‖v‖ = 1; slabCoord v x = ⟪v, x_h⟫; reason: same objects
--   - encoding: 'a smooth, everywhere positive, even density, a finite first moment, and mean zero'; dν/dπ ≤ 3, dπ/dν ≤ 100 → HasSmoothPosEvenDensity (C^∞ Lebesgue density); MeanZero (Bochner-integrable identity, integral 0); RatioBounds ν π 3 100 (mutual absolute continuity, a.e. bounds on the Radon–Nikodym derivatives); reason: the paper's definitions (§2.2 warmness: ν ≪ π and dν/dπ ≤ M π-a.e.)
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 57, Lemma 7.1 (PDF p. 60)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_7_1 :
    ∀ ϑ : ℝ → ℝ, IsSlabProfile ϑ →
      ForChosenConstants fun c => ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ Ξ ∈ Eadm c n, ∀ v : Point n, ‖v‖ = 1 →
          IsProbabilityMeasure (nuInit c ϑ Ξ v) ∧
          HasSmoothPosEvenDensity (nuInit c ϑ Ξ v) ∧
          MeanZero (nuInit c ϑ Ξ v) ∧
          ENNReal.ofReal (1 - 1 / Real.sqrt Real.pi) ≤ Zinit c ϑ Ξ v ∧ Zinit c ϑ Ξ v ≤ 1 ∧
          RatioBounds (nuInit c ϑ Ξ v) (piHard c Ξ) 3 100 ∧
          0.206 < 2 * (7 / 25) * Real.exp (-(7 / 25 : ℝ) ^ 2) / Real.sqrt (2 * Real.pi) ∧
          nuInit c ϑ Ξ v {x | |slabCoord v x| ≤ 9 / 20} ≤ ENNReal.ofReal (3 / 100) ∧
          ENNReal.ofReal (2 * (7 / 25) * Real.exp (-(7 / 25 : ℝ) ^ 2) / Real.sqrt (2 * Real.pi)) ≤
            piHard c Ξ {x | |slabCoord v x| ≤ 7 / 25} := by sorry

end SampQueryLB.WarmSLC
