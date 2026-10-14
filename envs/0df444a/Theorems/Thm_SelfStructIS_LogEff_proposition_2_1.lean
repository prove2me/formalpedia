-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_proposition_2_1
-- name    : SelfStructIS.LogEff.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:13.421064+00:00
-- url     : https://prove2.me/theorems/87643fcb-3bdd-47cd-9372-882aa6e91e23
-- title:
--   Proposition 2.1, p. 9 — ζ(u) is unbiased and T is invertible
-- statement:
--   Let $X$ have law $\mu$ with density $f_X$ on $\mathbb R^d$ ($d\ge 1$), let $L$ be a measurable loss, $\rho>0$, $u$ a threshold and $l$ a hyper-parameter, and let $T$, $J$ and $\zeta(u)$ be the self-structuring transformation, its Table 1 Jacobian and the single-sample estimator for the exponent $\kappa=\kappa^{(1)}$ or $\kappa=\kappa^{(2)}$. Assume $0<l\le u$, and $l>1$ when $\kappa=\kappa^{(2)}$. Assume further the support condition: for Lebesgue-almost every $x$, if $f_X(T(x))>0$ and $L(T(x))\ge u$, then $f_X(x)>0$. Then
--
--   1. the estimator is unbiased:
--   $$E[\zeta(u)]=p_u=P(L(X)\ge u);$$
--   2. $T$ is a bijection of $\mathbb R^d$;
--   3. there is a map $T^{-1}$ with $T(T^{-1}(x))=x$ for almost every $x\in\mathbb R^d$.
--
--   Unbiasedness of the sample mean $\bar\zeta_N(u)$ of $N$ independent copies follows by linearity. This is the basic validity property of Algorithm 1.
--
--   **Formalization Note** The proposition as printed ("for any $u>0$", $l\in[0,u]$) is false: for $d=1$, $X\sim\mathrm{Unif}[1,2]$, $\rho=1$, $u/l=100$ and $L(x)=ux$, the sampler moves all mass outside the support and $\zeta\equiv0$ while $p_u=1$. The hypotheses $0<l\le u$ ($l>1$ for $\kappa^{(2)}$) and the support condition are the ones the proof needs, and the support condition is also necessary. Bijectivity is what the proof on pp. 31–32 establishes, stated as an extra conjunct. $E[\zeta(u)]$ is a lower Lebesgue integral of the nonnegative $\zeta(u)$. $d\ge1$ is the paper's standing setting.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 9, Proposition 2.1 (proof pp. 31–32, App. A.2)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem proposition_2_1 (d : ℕ) (hd : 0 < d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (fX : (Fin d → ℝ) → ℝ) (hfX_meas : Measurable fX) (hfX_nonneg : ∀ x, 0 ≤ fX x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (fX x)))
    (L : (Fin d → ℝ) → ℝ) (hL : Measurable L) (ρ : ℝ) (hρ : 0 < ρ)
    (c : KappaChoice) (u l : ℝ) (hl : 0 < l) (hlu : l ≤ u) (hl_two : c = .two → 1 < l)
    (hsupp : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
      0 < fX (Tmap c ρ u l x) → u ≤ L (Tmap c ρ u l x) → 0 < fX x) :
    (∫⁻ x, ENNReal.ofReal (zeta c ρ fX L u l x) ∂μ = pu μ L u) ∧
      Function.Bijective (Tmap (d := d) c ρ u l) ∧
      ∃ Tinv : (Fin d → ℝ) → Fin d → ℝ,
        ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), Tmap c ρ u l (Tinv x) = x := by sorry

end SelfStructIS.LogEff
