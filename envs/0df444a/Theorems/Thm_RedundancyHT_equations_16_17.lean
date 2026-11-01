-- Prove2me | Theorems.Thm_RedundancyHT_equations_16_17
-- name    : RedundancyHT.equations_16_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:42.328688+00:00
-- url     : https://prove2.me/theorems/b108effa-f035-4e96-aa2b-04ffd3796395
-- title:
--   (16), (17), p.18: limits of the factors of (10) as $\lambda\uparrow\lambda^*$
-- statement:
--   Let $\mathcal T^*$ be the critical subset, $t_S\ge0$ and $z_S=\exp(-(1-\lambda/\lambda^*)t_S)$. There is $\epsilon>0$ such that for every non-empty $\mathcal T\ne\mathcal T^*$
--   $$\frac{N\lambda^*p_{\mathcal T}}{\mu_{\mathcal T}}=\frac{\mu_{\mathcal T^*}}{\mu_{\mathcal T}}\frac{p_{\mathcal T}}{p_{\mathcal T^*}}<1-\epsilon.$$
--   For every ordered vector $[S_1,\dots,S_m]$ of different job types and every $j$,
--   $$\lim_{\lambda\uparrow\lambda^*}\frac{N\lambda}{\mu(S_1,\dots,S_j)}p_{S_j}z_{S_j}=\frac{\mu_{\mathcal T^*}}{\mu(S_1,\dots,S_j)}\frac{p_{S_j}}{p_{\mathcal T^*}}\in(0,\infty),\tag{16}$$
--   and
--   $$\lim_{\lambda\uparrow\lambda^*}\Bigl(1-\frac{N\lambda}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}p_{S_i}z_{S_i}\Bigr)^{-1}=\begin{cases}\infty&\text{if }\{S_1,\dots,S_j\}=\mathcal T^*,\\ \bigl(1-\frac{\mu_{\mathcal T^*}}{\mu(S_1,\dots,S_j)}\sum_{i=1}^{j}\frac{p_{S_i}}{p_{\mathcal T^*}}\bigr)^{-1}\in(0,\infty)&\text{otherwise.}\end{cases}\tag{17}$$
--
--   The single diverging factor is the one at the position where the prefix of the vector equals $\mathcal T^*$. This is why only vectors passing through $\mathcal T^*$ survive in the limit.
--
--   Differences from the source:
--   - encoding: job types are the subsets S with λ_S > 0, arrival rates N λ p_S, speeds µ_n → a published Model with Fin n types, Fin m servers, p_S = nominal S / Σ nominal, load λ/µ and the hypothesis that every type has a compatible server; reason: nominal S := µ_tot p_S recovers every system of the paper, and the balance field of Model is only this normalization
--   - generalization: ε with N λ* p_𝒯/µ_𝒯 < 1 − ε for all 𝒯 ⊊ 𝒯* → the same for every non-empty 𝒯 ≠ 𝒯*; reason: (17) needs it for prefixes not contained in 𝒯*, and the printed claim for non-empty 𝒯 is the case 𝒯 ⊊ 𝒯*
--   - encoding: 𝒯 ⊊ 𝒯* includes 𝒯 = ∅ → non-empty 𝒯; reason: the ratio p_∅/µ_∅ is 0/0 on the page
--   - generalization: distinct job types are distinct subsets of servers → two indices of Fin n may have the same compatible servers; reason: the case of distinct subsets is the source's system, and no hypothesis is added
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, displays (16), (17) and the sentence above (17), p.18

import Definitions.Def_RedundancyHT_IsCriticalSubset
import Definitions.Def_RedundancyHT_lamStar
import Definitions.Def_RedundancyHT_muPrefix

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The factor limits (16), (17) and the ε claim above (17)** (arXiv:2005.14566v5, p.18), for
`z_S = exp(-(1 - λ/λ*) t_S)`, `t ≥ 0`.

**Formalization Note.** The page states the ε claim for `𝒯 ⊊ 𝒯*`, while (17) uses it for every
`{S₁,…,S_j} ≠ 𝒯*`, so it is stated for all non-empty `𝒯 ≠ 𝒯*`. The empty `𝒯` is out, since `ρ_∅` is
undefined. The value `∞` in (17) is `Tendsto … atTop`, along `𝓝[<] λ*`. -/
theorem equations_16_17 {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCriticalSubset D T) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    let ls := lamStar D T
    let z : ℝ → Fin n → ℝ := fun lam i => Real.exp (-(1 - lam / ls) * t i)
    (∃ ε : ℝ, 0 < ε ∧ ∀ A : Finset (Fin n), A.Nonempty → A ≠ T →
      (m : ℝ) * ls * pSet D A / muSet D A = muSet D T / muSet D A * (pSet D A / pSet D T) ∧
      muSet D T / muSet D A * (pSet D A / pSet D T) < 1 - ε) ∧
    ∀ (k : ℕ) (S : Fin k ↪ Fin n) (j : Fin k),
      let den : ℝ → ℝ := fun lam =>
        1 - (m : ℝ) * lam / muPrefix D S j *
          ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), pOf D (S i) * z lam (S i)
      let lim : ℝ := 1 - muSet D T / muPrefix D S j *
          ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), pOf D (S i) / pSet D T
      (Tendsto (fun lam => (m : ℝ) * lam / muPrefix D S j * pOf D (S j) * z lam (S j))
          (𝓝[<] ls) (𝓝 (muSet D T / muPrefix D S j * (pOf D (S j) / pSet D T))) ∧
        0 < muSet D T / muPrefix D S j * (pOf D (S j) / pSet D T)) ∧
      (prefixSet S j = T → Tendsto (fun lam => (den lam)⁻¹) (𝓝[<] ls) atTop) ∧
      (prefixSet S j ≠ T →
        Tendsto (fun lam => (den lam)⁻¹) (𝓝[<] ls) (𝓝 lim⁻¹) ∧ 0 < lim⁻¹) := by sorry

end RedundancyHT
