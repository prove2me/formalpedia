-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_8_2
-- name    : WildeQIT.PinskerRefined.theorem_10_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:10.406061+00:00
-- url     : https://prove2.me/theorems/c56b7757-18e0-47f8-b7a9-d338d4f08377
-- title:
--   Theorem 10.8.2 — $\frac{2}{\ln 2}\Delta^2\le I(X;Y)\le\Delta\log(\min\{|\mathcal X|,|\mathcal Y|\}-1)+h_2(\Delta)$
-- statement:
--   Let $X$ and $Y$ be discrete random variables on finite alphabets $\mathcal X$ and $\mathcal Y$ with joint distribution $p_{XY}$, and let $p_X\otimes p_Y$ be the product of their marginals. Let
--
--   $$
--   \Delta=\tfrac12\,\|p_{XY}-p_X\otimes p_Y\|_1 .
--   $$
--
--   Then
--
--   $$
--   I(X;Y)\ge\frac{2}{\ln 2}\,\Delta^2 \tag{10.144}
--   $$
--
--   and
--
--   $$
--   I(X;Y)\le\Delta\log\bigl(\min\{|\mathcal X|,|\mathcal Y|\}-1\bigr)+h_2(\Delta), \tag{10.145}
--   $$
--
--   where $\log$ is base $2$ and $h_2$ is the binary entropy. The mutual information is therefore small exactly when $X$ and $Y$ are nearly independent in trace distance, which quantifies the saturation condition of the non-negativity of mutual information.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. When $\min\{|\mathcal X|,|\mathcal Y|\}=1$ the term $\log 0$ is Lean's $\log_2 0=0$; then $\Delta=0$, so the product is $0$, the book's value under $0\log 0=0$.
--
--   Differences from the source:
--
--   - encoding: log(min{|X|, |Y|} − 1) at min{|X|, |Y|} = 1 → Real.logb 2 0 = 0; reason: in that case Δ = 0, so Δ · log(0) is 0 under the book’s 0 log 0 = 0; no instance changes
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.8.2, pp. 312–313, Eqs. (10.144)–(10.145)

import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_WildeQIT_classicalTraceDist

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.8.2**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 312–313: for discrete random variables `X, Y` with joint
distribution `p_{XY}` on `𝒳 × 𝒴` and `∆ = ½ ‖p_{XY} − p_X ⊗ p_Y‖₁`,
`I(X;Y) ≥ (2 / ln 2) ∆²` (10.144) and `I(X;Y) ≤ ∆ log(min{|𝒳|, |𝒴|} − 1) + h₂(∆)` (10.145).

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). `I(X;Y)` is `mutualInfo`, `h₂` is `binaryEntropy`, `‖·‖₁` is
`classicalTraceDist`, and `p_X ⊗ p_Y` is `p.fst.prod p.snd`. `log` is `Real.logb 2` and `|𝒳|` is
`Fintype.card`; when `min{|𝒳|, |𝒴|} = 1` the term `log 0` is Lean's `logb 2 0 = 0`, and then
`∆ = 0`, so (10.145) reads `I(X;Y) ≤ 0`, the book's value with `0 · log 0 = 0`. -/
theorem theorem_10_8_2 {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) :
    let Δ : ℝ := 1 / 2 * classicalTraceDist p.prob (p.fst.prod p.snd).prob
    2 / Real.log 2 * Δ ^ 2 ≤ mutualInfo p ∧
      mutualInfo p ≤
        Δ * Real.logb 2 (((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) - 1) +
          binaryEntropy Δ := by sorry

end WildeQIT.PinskerRefined
