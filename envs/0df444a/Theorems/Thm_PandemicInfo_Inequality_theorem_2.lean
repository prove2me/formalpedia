-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_theorem_2
-- name    : PandemicInfo.Inequality.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:08.136515+00:00
-- url     : https://prove2.me/theorems/2bcd08e9-a1ad-4559-93c9-43029b2113d2
-- title:
--   Theorem 2, p. 12 (PDF 13) — $\lambda_1$–$\lambda_4$ nonincreasing in $\sigma$; optimal exaggeration probability decreasing, downplaying probability increasing in $\sigma$
-- statement:
--   **Theorem 2 (effect of economic inequality).** Let $\sigma<\sigma'$ be two levels of economic inequality, every other parameter fixed, with the standing assumptions holding at both levels. Then:
--
--   1. the thresholds do not increase: $\lambda_i(\sigma')\le\lambda_i(\sigma)$ for $i=1,\dots,4$;
--   2. if $\lambda\in[0,1]$ lies in the exaggeration region at both levels ($\lambda_1<\lambda<\lambda_2$ and $\mu^\circ<\mu^{EX}_\lambda$), and the binary exaggerating policies with $\pi(m_h\mid\omega_h)=1$ and exaggeration probabilities $\pi^\star(m_h\mid\omega_\ell)$ and $\pi'^\star(m_h\mid\omega_\ell)$ are optimal at $\sigma$ and $\sigma'$ respectively, then
--   $$\pi'^\star(m_h\mid\omega_\ell)<\pi^\star(m_h\mid\omega_\ell);$$
--   3. if $\lambda\in[0,1]$ lies in the downplaying region at both levels ($\lambda_3<\lambda<\lambda_4$ and $\mu^\circ>\mu^{DP}_\lambda$), and the binary downplaying policies with $\pi(m_\ell\mid\omega_\ell)=1$ and downplaying probabilities $\pi^\star(m_\ell\mid\omega_h)$ and $\pi'^\star(m_\ell\mid\omega_h)$ are optimal at $\sigma$ and $\sigma'$ respectively, then
--   $$\pi^\star(m_\ell\mid\omega_h)<\pi'^\star(m_\ell\mid\omega_h).$$
--
--   In words: the more unequal the economic impact of the epidemic, the less the government exaggerates and the more it downplays its severity.
--
--   **Formalization Note** Optimality is for the government's problem (6) over all finite-message policies and BNE profiles (`IsOptimalPolicy`); the probabilities are not replaced by the formulas (17)–(18) of the proof. Theorem 2 says "decreasing"/"increasing" for the probabilities and "non-increasing" for the thresholds; the Lean is strict and weak respectively. The thresholds are the sentinel forms of the definition file, which agree with the paper's for every $\lambda\in[0,1]$. The proof of Theorem 2 in the paper attaches the downplaying probability to $\lambda_1<\lambda<\lambda_2$ and the exaggerating one to $\lambda_3<\lambda<\lambda_4$; the statement here uses the regimes of Theorem 1. All statements assume the standing assumptions of §2 (`Params.Standing`) at both $\sigma$ and $\sigma'$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 12 (PDF 13), Theorem 2

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Theorem 2, p. 12 (effect of economic inequality): raising `σ` to `σ'` (all other parameters
fixed, both admissible) does not raise the thresholds `λ1, …, λ4`; when exaggerating is optimal at
both levels the optimal exaggeration probability `π⋆(m_h | ω_ℓ)` strictly decreases, and when
downplaying is optimal at both levels the optimal downplaying probability `π⋆(m_ℓ | ω_h)` strictly
increases. -/
theorem theorem_2 (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing)
    (hS' : ({ P with σ := σ' } : Params).Standing) :
    (({ P with σ := σ' } : Params).lam1 ≤ P.lam1 ∧ ({ P with σ := σ' } : Params).lam2 ≤ P.lam2 ∧
      ({ P with σ := σ' } : Params).lam3 ≤ P.lam3 ∧ ({ P with σ := σ' } : Params).lam4 ≤ P.lam4) ∧
    (∀ lam pl pl' : ℝ, 0 ≤ lam → lam ≤ 1 →
      P.lam1 < lam → lam < P.lam2 → P.μ0 < P.μEX lam →
      ({ P with σ := σ' } : Params).lam1 < lam → lam < ({ P with σ := σ' } : Params).lam2 →
      ({ P with σ := σ' } : Params).μ0 < ({ P with σ := σ' } : Params).μEX lam →
      P.IsOptimalPolicy lam (binPolicy pl 1) →
      ({ P with σ := σ' } : Params).IsOptimalPolicy lam (binPolicy pl' 1) →
      1 - pl' < 1 - pl) ∧
    (∀ lam ph ph' : ℝ, 0 ≤ lam → lam ≤ 1 →
      P.lam3 < lam → lam < P.lam4 → P.μDP lam < P.μ0 →
      ({ P with σ := σ' } : Params).lam3 < lam → lam < ({ P with σ := σ' } : Params).lam4 →
      ({ P with σ := σ' } : Params).μDP lam < ({ P with σ := σ' } : Params).μ0 →
      P.IsOptimalPolicy lam (binPolicy 1 ph) →
      ({ P with σ := σ' } : Params).IsOptimalPolicy lam (binPolicy 1 ph') →
      1 - ph < 1 - ph') := by sorry

end PandemicInfo.Inequality
