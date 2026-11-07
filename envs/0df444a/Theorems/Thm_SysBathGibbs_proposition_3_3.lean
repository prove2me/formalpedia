-- Prove2me | Theorems.Thm_SysBathGibbs_proposition_3_3
-- name    : SysBathGibbs.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:37.842207+00:00
-- url     : https://prove2.me/theorems/e94f3e80-0ac0-483e-acbe-6db02659d2b6
-- title:
--   Proposition 3.3 — Second-order state dynamics: $\mathcal L_{x,T}$ is a trace-preserving Lindbladian
-- statement:
--   Let $H_n$ be a nearest-neighbor chain as in (1.2), $\sigma=\beta/2$, $T>0$ and $x\in[n]$. With the site transition map $\mathcal J_{x,T}$, the ordered coefficient $Q_{x,T}$, the decay matrix $M_{x,T}$ and the coherent term $H_{x,T}=(Q_{x,T}-Q_{x,T}^\dagger)/(2i)$ of (3.14)–(3.16), all over the window $(-T,T)$:
--
--   1. $M_{x,T}=Q_{x,T}+Q_{x,T}^\dagger$ and $Q_{x,T}=\tfrac12M_{x,T}+iH_{x,T}$, and $H_{x,T}$ is Hermitian;
--   2. for every $\rho$, the site generator (3.8) satisfies
--   $$
--   \mathcal L_{x,T}(\rho)=\mathcal J_{x,T}(\rho)-Q_{x,T}\rho-\rho Q_{x,T}^\dagger=-i[H_{x,T},\rho]+\sum_{a=1}^{Q}\int_{\mathbb R}g_{\beta,\sigma}(u)\,\mathcal D_{V_{A_{x,a},T}(u)}(\rho)\,du;
--   $$
--   3. $\mathcal L_{x,T}(\rho)=-i[H_{x,T},\rho]+\mathcal J_{x,T}(\rho)-\tfrac12\{M_{x,T},\rho\}$, and $\operatorname{Tr}\mathcal L_{x,T}(\rho)=0$.
--
--   So $\mathcal L_{x,T}$ is a trace-preserving Lindbladian with transition map $\mathcal J_{x,T}$, decay part $-\tfrac12\{M_{x,T},\cdot\}$ and coherent term $H_{x,T}$. This identifies the second-order term of the interaction-picture channel.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: "L_{x,T} is a trace-preserving Lindbladian with transition map J, decay part −½{M,·}, coherent term H" → the three identities, Hermiticity of H_{x,T} and Tr L_{x,T}(ρ) = 0; reason: these are the clauses of the Lindblad form (2.15); the weight g is nonnegative by definition
--   - encoding: ρ a state → ρ any complex matrix; reason: (3.8), (3.14) are linear formulas in ρ; the identities on all matrices contain those on states
--   - encoding: a chain [n] of qudits of dimension 2^q → q ≥ 1 as a hypothesis; reason: a qudit has q ≥ 1 qubits
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Proposition 3.3 (eqs. (3.14)–(3.17)), p.24

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Proposition 3.3 (Second-order state dynamics)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.24.
For a nearest-neighbor chain, `T > 0` and a site `x`: `M = Q + Q†`, `Q = ½M + iH`, `H` is Hermitian, and
the site generator (3.8) equals `J(ρ) - Qρ - ρQ†`, equals `-i[H, ρ] + ∑_a ∫ g(u) D_{V(u)}(ρ) du`, and
has the Lindblad form with transition map `J`, decay part `-½{M, ·}` and coherent term `H`; it is trace
preserving.

**Formalization Note.** `ρ` is any matrix, since (3.8) and (3.14) are linear formulas in `ρ`. -/
theorem proposition_3_3 :
    ∀ (β : ℝ), 0 < β → ∀ (n q : ℕ), 1 ≤ q → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
      ∀ (T : ℝ), 0 < T → ∀ x : Fin n,
        siteM β h x (finWin T) = siteQ β h x (finWin T) + (siteQ β h x (finWin T))ᴴ ∧
        siteQ β h x (finWin T) =
          (1 / 2 : ℂ) • siteM β h x (finWin T) + Complex.I • siteH β h x (finWin T) ∧
        (siteH β h x (finWin T))ᴴ = siteH β h x (finWin T) ∧
        ∀ ρ : SysMat n q,
          siteGen β h x (finWin T) ρ =
            siteJ β h x (finWin T) ρ - siteQ β h x (finWin T) * ρ -
              ρ * (siteQ β h x (finWin T))ᴴ ∧
          siteGen β h x (finWin T) ρ =
            (-Complex.I) • comm (siteH β h x (finWin T)) ρ + siteDiss β h x (finWin T) ρ ∧
          siteGen β h x (finWin T) ρ =
            (-Complex.I) • comm (siteH β h x (finWin T)) ρ + siteJ β h x (finWin T) ρ -
              (1 / 2 : ℂ) • acomm (siteM β h x (finWin T)) ρ ∧
          Matrix.trace (siteGen β h x (finWin T) ρ) = 0 := by sorry

end SysBathGibbs
