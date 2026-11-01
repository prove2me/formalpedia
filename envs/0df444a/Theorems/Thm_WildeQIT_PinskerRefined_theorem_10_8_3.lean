-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_8_3
-- name    : WildeQIT.PinskerRefined.theorem_10_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:35.945173+00:00
-- url     : https://prove2.me/theorems/fd58e875-1b73-4323-989e-c6889390ebf0
-- title:
--   Theorem 10.8.3 — $\frac{2}{\ln 2}\Delta^2\le I(X;Y|Z)\le\Delta\log(\min\{|\mathcal X|,|\mathcal Y|\}-1)+h_2(\Delta)$
-- statement:
--   Let $X$, $Y$ and $Z$ be discrete random variables on finite alphabets $\mathcal X$, $\mathcal Y$ and $\mathcal Z$ with joint distribution $p_{XYZ}$, and let $p_{X|Z}\,p_{Y|Z}\,p_Z$ be the distribution corresponding to the Markov chain $X - Z - Y$, with mass $p_{XZ}(x,z)\,p_{YZ}(y,z)/p_Z(z)$ at $(x,y,z)$. Let
--
--   $$
--   \Delta=\tfrac12\,\bigl\|p_{XYZ}-p_{X|Z}\,p_{Y|Z}\,p_Z\bigr\|_1 .
--   $$
--
--   Then
--
--   $$
--   I(X;Y|Z)\ge\frac{2}{\ln 2}\,\Delta^2 \tag{10.158}
--   $$
--
--   and
--
--   $$
--   I(X;Y|Z)\le\Delta\log\bigl(\min\{|\mathcal X|,|\mathcal Y|\}-1\bigr)+h_2(\Delta), \tag{10.159}
--   $$
--
--   where $\log$ is base $2$ and $h_2$ is the binary entropy.
--
--   The conditional mutual information is small exactly when $p_{XYZ}$ is close in trace distance to a Markov chain $X - Z - Y$: this is the near-saturation version of strong subadditivity (Theorem 10.6.1), with both directions quantified.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. The Markov law is `markovLaw p`, defined as $0$ where $p_Z(z)=0$. When $\min\{|\mathcal X|,|\mathcal Y|\}=1$ the term $\log 0$ is Lean's $\log_2 0=0$; then $\Delta=0$, so the product is $0$, the book's value under $0\log 0=0$.
--
--   Differences from the source:
--
--   - encoding: p_{X|Z} p_{Y|Z} p_Z at z with p_Z(z) = 0 → 0; reason: the conditionals are undefined there and p_XZ(x,z) = p_YZ(y,z) = 0, so 0 is the only value that makes it a distribution; same Δ for every instance
--   - encoding: log(min{|X|, |Y|} − 1) at min{|X|, |Y|} = 1 → Real.logb 2 0 = 0; reason: in that case Δ = 0, so Δ · log(0) is 0 under the book’s 0 log 0 = 0; no instance changes
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.8.3, p. 314, Eqs. (10.158)–(10.159)

import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_WildeQIT_classicalTraceDist
import Definitions.Def_WildeQIT_PinskerRefined_markovLaw

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.8.3**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 314: for discrete random variables `X, Y, Z` with joint
distribution `p_{XYZ}` on `𝒳 × 𝒴 × 𝒵`, and the Markov law `p_{X|Z} p_{Y|Z} p_Z` of `X − Z − Y`, with
`∆ = ½ ‖p_{XYZ} − p_{X|Z} p_{Y|Z} p_Z‖₁`,
`I(X;Y|Z) ≥ (2 / ln 2) ∆²` (10.158) and `I(X;Y|Z) ≤ ∆ log(min{|𝒳|, |𝒴|} − 1) + h₂(∆)` (10.159).

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). `I(X;Y|Z)` is `condMutualInfo` (Definition 10.6.1), `h₂` is
`binaryEntropy`, `‖·‖₁` is `classicalTraceDist`, and `p_{X|Z} p_{Y|Z} p_Z` is `markovLaw p`,
`(x,y,z) ↦ p_{XZ}(x,z) p_{YZ}(y,z) / p_Z(z)`, which is `0` where `p_Z(z) = 0`. `log` is `Real.logb 2`
and `|𝒳|` is `Fintype.card`; when `min{|𝒳|, |𝒴|} = 1` the term `log 0` is `logb 2 0 = 0`, and then
`∆ = 0`. -/
theorem theorem_10_8_3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) :
    let Δ : ℝ := 1 / 2 * classicalTraceDist p.prob (markovLaw p).prob
    2 / Real.log 2 * Δ ^ 2 ≤ condMutualInfo p ∧
      condMutualInfo p ≤
        Δ * Real.logb 2 (((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) - 1) +
          binaryEntropy Δ := by sorry

end WildeQIT.PinskerRefined
