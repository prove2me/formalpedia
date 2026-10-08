-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_cvar_eq_sorted
-- name    : RiskUncSets.Distortion.cvar_eq_sorted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:58.827103+00:00
-- url     : https://prove2.me/theorems/62334bbb-1e42-48a5-9a44-90e88c570a11
-- title:
--   Proof of Theorem 4.2, p. 1489 — CVaR_α(X) = sup{E_q[−X] : q ∈ Δᴺ, qᵢ ≤ 1/(Nα)} = −Σ q^α_i x₍ᵢ₎ with q^α ∈ Δ̂ᴺ
-- statement:
--   Let $N \ge 1$, let $\Omega$ carry the uniform distribution, and let $\alpha \in (0, 1]$ and $X \in \mathbb R^N$ with increasing order statistics $x_{(1)} \le \cdots \le x_{(N)}$. Let $q^\alpha \in \mathbb R^N$ have entries $1/(N\alpha)$ in positions $1, \dots, \lfloor N\alpha \rfloor$, the entry $(N\alpha - \lfloor N\alpha\rfloor)/(N\alpha)$ in position $\lfloor N\alpha\rfloor + 1$ (if $\lfloor N\alpha \rfloor < N$), and $0$ elsewhere. Then
--   $$\mathrm{CVaR}_\alpha(X) = \sup_{\{q \in \Delta^N :\ q_i \le 1/(N\alpha)\}} \mathbb E_q[-X] = -\sum_{i=1}^N q^\alpha_i x_{(i)},$$
--   the supremum being a least upper bound, and $q^\alpha \in \hat\Delta^N$.
--
--   This identifies $\mathrm{CVaR}_\alpha$ as a risk measure of the form (4); integrating $q^\alpha$ against the mixing measure of Lemma 4.1 gives the "only if" direction of Theorem 4.2.
--
--   **Formalization Note** The page prints the coefficient of $x_{(\lceil N\alpha\rceil)}$ as $(N\alpha - \lfloor N\alpha\rfloor)/\lfloor N\alpha\rfloor$; the mass left after $\lfloor N\alpha\rfloor$ weights $1/(N\alpha)$ is $(N\alpha - \lfloor N\alpha\rfloor)/(N\alpha)$, which the statement uses. The page states the display "for $\alpha \ge 1/N$" and adds "for $\alpha < 1/N$, we have $q^\alpha = q^{1/N}$"; the statement covers every $\alpha \in (0,1]$ at once, since for $\alpha < 1/N$ the vector $q^\alpha$ above is $(1, 0, \dots, 0) = q^{1/N}$. Indices are 0-based: `cvarWeight N α` has $1/(N\alpha)$ at indices $i$ with $i + 1 \le \lfloor N\alpha\rfloor$ and the remainder at index $\lfloor N\alpha \rfloor$. Order statistics are `X ∘ Tuple.sort X`.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1489, proof of Theorem 4.2, CVaR display and q^α

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem cvar_eq_sorted {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (X : Fin N → ℝ) :
    IsLUB ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) ''
        {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)})
        (cvar (uniform N) α X) ∧
      cvar (uniform N) α X = -∑ i, cvarWeight N α i * X (Tuple.sort X i) ∧
      cvarWeight N α ∈ restrictedSimplex N := by sorry

end RiskUncSets.Distortion
