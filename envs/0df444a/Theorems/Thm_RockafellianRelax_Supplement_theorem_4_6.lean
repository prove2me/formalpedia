-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_4_6
-- name    : RockafellianRelax.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:19:28.756117+00:00
-- url     : https://prove2.me/theorems/834a08d6-1e62-4757-95b4-2d2fbb0cf882
-- title:
--   Theorem 4.6 — exactness of the $\ell_1$-penalized Rockafellian for large $\theta$
-- statement:
--   Let $f_i : \mathbb R^n\to\overline{\mathbb R}$, $i = 0,1,\dots,s$, be proper and lower semicontinuous, let $p \in \Delta = \{q\in[0,\infty)^s \mid \sum_i q_i = 1\}$, and let $\varphi = f_0 + \sum_{i=1}^s p_i f_i$ be the objective of the actual problem (2.1), with $0\cdot\infty = 0$. Suppose that $\eta\ge0$ and $\bar x\in\mathbb R^n$ satisfy $f_i(\bar x)<\infty$ and $\inf_xf_i(x)\ge-\eta$ for $i=0,1,\dots,s$. For $\theta\ge0$ and $q\in\Delta$ let
--
--   $$
--   F_{q,\theta}(u,x)=f_0(x)+\sum_{i=1}^s(q_i+u_i)f_i(x)+\theta\|u\|_1
--   $$
--
--   if $q+u\in\Delta$, and $+\infty$ otherwise. Thus $f=F_{p,\theta}$ is (4.11) and $f^\nu=F_{p^\nu,\theta}$ is (4.12). Then there is $\theta_0\ge0$ such that for every $\theta\ge\theta_0$:
--
--   1. $f$ is a strictly exact Rockafellian for $\varphi$, supported by $0\in\mathbb R^s$;
--   2. for every sequence $p^\nu\in\Delta$ with $\|p^\nu-p\|_2\to0$, the functions $f^\nu$ epi-converge to $f$ and are strictly limit-exact Rockafellians for $\varphi$, supported by $0$.
--
--   This Rockafellian needs no knowledge of the rate at which $p^\nu$ tends to $p$.
--
--   **Formalization Note** The threshold $\theta_0$ is chosen before the sequence $p^\nu$. The infimum conditions are written pointwise and include $i=0$.
--
--   Differences from the source:
--
--   - reading: if θ is sufficiently large → ∃ θ₀ ≥ 0, ∀ θ ≥ θ₀, with θ₀ chosen before the sequence p^ν; reason: the first claim has no sequence and the second refers to the same θ; this is the stronger reading and the one the proof gives
--   - reading: strictly limit-exact Rockafellians, with no support named in the last clause → supported by 0 ∈ ℝˢ; reason: by Definition 3.6 the support is that of f, which the theorem states to be 0
--   - encoding: strictly limit-exact Rockafellians with f as their limit → epi-convergence to this f and strict exactness of this f, stated next to IsStrictlyLimitExact; reason: the published predicate quantifies the limit existentially, while the paper names it
--   - encoding: f_i(x̄) < ∞ and inf_x f_i(x) ≥ −η for i = 0, …, s → separate hypotheses for f₀ and for Fin s, with the infimum bound written pointwise; reason: equivalent forms
--   - encoding: sums containing indicator functions, under ∞ − ∞ = ∞ → definitions by cases: the formula on the feasible set, +∞ elsewhere; reason: EReal has −∞ + ∞ = −∞, and the cases give exactly the paper's values
--   - encoding: ℝⁿ, R̄, i = 1, …, s, ν ∈ ℕ = {1, 2, …}, sequential lower semicontinuity → Fin n → ℝ, EReal, Fin s, ν from 0, LowerSemicontinuous; reason: Lean conventions with the same instances; the two notions of lower semicontinuity agree on ℝⁿ
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.6, p.17, with displays (4.11)–(4.12), p.17

import Mathlib
import Definitions.Def_PerspEpi_SeqEpiConv
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_IsStrictlyLimitExact
import Definitions.Def_RockafellianRelax_Supplement_IsProper
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_l1Rockafellian
open Filter Topology

namespace RockafellianRelax.Supplement

/-- **Theorem 4.6 (exactness under alternative Rockafellian).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.6, p.17: "In the
setting of Subsection 4.1 with p, pν ∈ ∆ and proper lsc f_i : ℝⁿ → R̄, i = 0, 1, …, s, consider f
from (4.11) and fν from (4.12). Suppose that there are η ∈ [0, ∞) and x̄ ∈ ℝⁿ such that
f_i(x̄) < ∞ and inf_x f_i(x) ≥ −η, i = 0, 1, …, s. If θ is sufficiently large, then the
Rockafellian f is strictly exact, supported by 0 ∈ ℝˢ, and, under the additional assumption that
‖pν − p‖₂ → 0, the approximating functions {fν, ν ∈ ℕ} are strictly limit-exact Rockafellians with
f as their limit."

**Formalization Note.** "θ sufficiently large" is `∃ θ₀ ≥ 0, ∀ θ ≥ θ₀`, with `θ₀` chosen before
the sequence `pν`. The conditions on `η` and `x̄` include `i = 0`; `inf_x fᵢ(x) ≥ −η` is written
pointwise. The limit is named: epi-convergence to `f` is stated next to strict limit-exactness,
whose support is the same `0`. -/
theorem theorem_4_6 {n s : ℕ} (f0 : (Fin n → ℝ) → EReal) (fi : Fin s → (Fin n → ℝ) → EReal)
    (p : Fin s → ℝ) (hp : p ∈ stdSimplex ℝ (Fin s))
    (hf0 : IsProper f0) (hf0lsc : LowerSemicontinuous f0)
    (hfi : ∀ i, IsProper (fi i)) (hfilsc : ∀ i, LowerSemicontinuous (fi i))
    (η : ℝ) (hη : 0 ≤ η) (xbar : Fin n → ℝ)
    (hxbar0 : f0 xbar < ⊤) (hxbar : ∀ i, fi i xbar < ⊤)
    (hlow0 : ∀ x, ((-η : ℝ) : EReal) ≤ f0 x) (hlow : ∀ i x, ((-η : ℝ) : EReal) ≤ fi i x) :
    ∃ θ0 : ℝ, 0 ≤ θ0 ∧ ∀ θ : ℝ, θ0 ≤ θ →
      IsStrictlyExact (l1Rockafellian f0 fi p θ) (expObjective f0 fi p) 0 ∧
        ∀ pseq : ℕ → Fin s → ℝ, (∀ ν, pseq ν ∈ stdSimplex ℝ (Fin s)) →
          Tendsto (fun ν => euclidNorm (pseq ν - p)) atTop (𝓝 0) →
          PerspEpi.SeqEpiConv (fun ν => l1Rockafellian f0 fi (pseq ν) θ)
              (l1Rockafellian f0 fi p θ) ∧
            IsStrictlyLimitExact (fun ν => l1Rockafellian f0 fi (pseq ν) θ)
              (expObjective f0 fi p) 0 := by sorry

end RockafellianRelax.Supplement
