-- Prove2me | Theorems.Thm_PrimalDualLDR_RandomRecourse_proposition_6
-- name    : PrimalDualLDR.RandomRecourse.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:42.652731+00:00
-- url     : https://prove2.me/theorems/fb26facf-75e3-4c74-97f7-9c83e98c9db6
-- title:
--   Proposition 6 — an S-lemma certificate S − Σ λ_ℓ W_ℓ ⪰ 0 implies ξᵀSξ ≥ 0 P-a.s.; the converse holds for l = 1
-- statement:
--   Assume the standing assumptions of §3: $\Xi=\{\xi:\ e_1^\top\xi=1,\ \xi^\top W_\ell\xi\ge0,\ \ell=1,\dots,l\}$ with symmetric $W_1,\dots,W_l$ is the support of the probability measure $\mathbb P$, and it is nonempty, bounded and spans $\mathbb R^k$. Fix a symmetric $k\times k$ matrix $S$ and consider
--
--   1. (i) there is $\lambda\in\mathbb R^l$ with $\lambda\ge0$ and $S-\sum_{\ell=1}^l\lambda_\ell W_\ell\succeq0$;
--   2. (ii) $\xi^\top S\xi\ge0$ $\mathbb P$-almost surely.
--
--   Then, for every $l$, (i) implies (ii); and if $l=1$, (ii) implies (i):
--   $$
--   \text{(i)}\Longrightarrow\text{(ii)},\qquad l=1:\ \text{(ii)}\Longrightarrow\text{(i)} .
--   $$
--
--   Applied to each slack matrix $S_\mu$, this replaces the semi-infinite inequality constraints of $\mathcal{SP}^u$ by linear matrix inequalities; it is why (3.14) is a conservative approximation of $\mathcal{SP}^u$ in general and an exact one when $l=1$.
--
--   **Formalization Note** (ii) is stated $\mathbb P$-almost surely, as printed. $\succeq0$ is Mathlib's `PosSemidef`; $\lambda\ge0$ is componentwise.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 12, Proposition 6

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Setting

open MeasureTheory Matrix

namespace PrimalDualLDR.RandomRecourse

/-- **Kuhn, Wiesemann, Georghiou (preprint 2009), Proposition 6, p. 12.** Under the standing
assumptions of §3, for a fixed symmetric `S ∈ 𝕊` consider
(i) `∃ λ ∈ ℝ^l, λ ≥ 0, S − Σ_ℓ λ_ℓ W_ℓ ⪰ 0`; (ii) `ξᵀSξ ≥ 0` `P`-almost surely.
For every `l`, (i) implies (ii); if `l = 1`, (ii) implies (i). -/
theorem proposition_6 (σ : Setting) (hσ : σ.Standing)
    (S : Matrix (Fin σ.k) (Fin σ.k) ℝ) (hS : S.IsSymm) :
    ((∃ lam : Fin σ.l → ℝ, (∀ ℓ, 0 ≤ lam ℓ) ∧ (S - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ).PosSemidef) →
        ∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) ∧
      (σ.l = 1 → (∀ᵐ ξ ∂σ.P, 0 ≤ ξ ⬝ᵥ (S *ᵥ ξ)) →
        ∃ lam : Fin σ.l → ℝ, (∀ ℓ, 0 ≤ lam ℓ) ∧ (S - ∑ ℓ : Fin σ.l, lam ℓ • σ.W ℓ).PosSemidef) := by sorry

end PrimalDualLDR.RandomRecourse
