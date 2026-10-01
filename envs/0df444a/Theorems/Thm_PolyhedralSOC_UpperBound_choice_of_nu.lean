-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_choice_of_nu
-- name    : PolyhedralSOC.UpperBound.choice_of_nu
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:49:55.628908+00:00
-- url     : https://prove2.me/theorems/a4f8107e-47f2-4241-ae3b-82ea5bf4fa6c
-- title:
--   Proof of Theorem 1.1 — $\nu_\ell=\lfloor c\,\ell\ln(2/\varepsilon)\rfloor$ gives $\beta\le\varepsilon$ at cost $O(k\ln(2/\varepsilon))$
-- statement:
--   There are absolute constants $c>0$ and $C>0$ such that the following holds for every $\theta\ge1$ and every $\varepsilon\in(0,1]$. Set
--   $$\nu_\ell=\Big\lfloor c\,\ell\ln\frac{2}{\varepsilon}\Big\rfloor,\qquad \ell=1,\dots,\theta.$$
--   Then
--   1. every $\nu_\ell$ is a positive integer;
--   2. $\displaystyle\beta(\nu_1,\dots,\nu_\theta)=\prod_{\ell=1}^{\theta}\frac{1}{\cos\big(\frac{\pi}{2^{\nu_\ell+1}}\big)}-1\le\varepsilon;$
--   3. $\displaystyle\sum_{\ell=1}^{\theta}2^{\theta-\ell}\nu_\ell\le C\,2^\theta\ln\frac{2}{\varepsilon}.$
--
--   With $k=2^\theta$, item 3 is the estimate that turns the size bounds $p\le k+O(1)\sum_\ell 2^{\theta-\ell}\nu_\ell$ and $q\le O(1)\sum_\ell 2^{\theta-\ell}\nu_\ell$ of the approximation (10) into $p,q\le O(1)\,k\ln(2/\varepsilon)$, as claimed in Theorem 1.1.
--
--   **Formalization Note** The paper writes $\nu_\ell=\lfloor O(1)\,\ell\ln(2/\varepsilon)\rfloor$ "with properly chosen absolute constant $O(1)$"; here that constant is the existential $c$, chosen before $\theta$ and $\varepsilon$, and $C$ likewise. Item 1 is explicit because the construction (8) needs positive integers. The paper's conclusion is stated for $p$ and $q$; since those depend on how (10) is encoded as a linear map, this statement records the arithmetic estimate on $\sum_\ell 2^{\theta-\ell}\nu_\ell$ that the paper's size bounds reduce to.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, p. 201, choice of ν_ℓ

import Mathlib

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, p. 201 (PDF p. 9): with a
properly chosen absolute constant `c`, setting `ν_ℓ = ⌊c ℓ ln(2/ε)⌋` (`ℓ = 1, …, θ`) for
`ε ∈ (0, 1]` gives positive integers `ν_ℓ` with
`β(ν_1, …, ν_θ) = ∏_{ℓ=1}^θ 1/cos(π/2^{ν_ℓ+1}) − 1 ≤ ε` and
`∑_{ℓ=1}^θ 2^{θ−ℓ} ν_ℓ ≤ C · 2^θ · ln(2/ε)` for an absolute constant `C`; the latter is the
quantity that bounds `p(k, ν_1, …, ν_θ)` and `q(k, ν_1, …, ν_θ)` (properties 1–2, pp. 200–201). -/
theorem choice_of_nu :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ θ : ℕ, 1 ≤ θ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → 1 ≤ ⌊c * ℓ * Real.log (2 / ε)⌋₊) ∧
        (∏ ℓ ∈ Finset.Icc 1 θ,
            1 / Real.cos (Real.pi / 2 ^ (⌊c * ℓ * Real.log (2 / ε)⌋₊ + 1))) - 1 ≤ ε ∧
        ((∑ ℓ ∈ Finset.Icc 1 θ, 2 ^ (θ - ℓ) * ⌊c * ℓ * Real.log (2 / ε)⌋₊ : ℕ) : ℝ)
          ≤ C * 2 ^ θ * Real.log (2 / ε) := by sorry

end PolyhedralSOC.UpperBound
