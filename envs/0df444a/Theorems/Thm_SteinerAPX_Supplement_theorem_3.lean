-- Prove2me | Theorems.Thm_SteinerAPX_Supplement_theorem_3
-- name    : SteinerAPX.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:13:46.319437+00:00
-- url     : https://prove2.me/theorems/bd459489-a329-4d13-bcaa-1d5083ba7793
-- title:
--   Theorem 3 — under weak ETH, no $(1+\varepsilon)$-approximation in $\mathbb R^d$ in time $2^{O(\varepsilon^{-\gamma(d-1)})}\mathrm{poly}(n)$, any $d\ge2$, $\gamma<1$
-- statement:
--   Assume weak ETH (Hypothesis 1). Let $d \ge 2$ be an integer and $\gamma < 1$ a real number. Then there is no algorithm that, given a rational accuracy $0<\varepsilon<1$ and a set of $n\ge2$ distinct rational points in $\mathbb R^d$, outputs a network of segments connecting all the points of length at most $(1+\varepsilon)\,\mathrm{OPT}$ and runs in time
--   $$2^{\,C\,\varepsilon^{-\gamma(d-1)}}\cdot \ell^{\,O(1)}$$
--   for a constant $C$, where $\ell$ is the input length; and there is no such algorithm that outputs a rational $v$ with $\mathrm{OPT}\le v\le(1+\varepsilon)\,\mathrm{OPT}$.
--
--   Since the known approximation scheme runs in time $2^{O(\varepsilon^{-(d-1)})}\,\mathrm{poly}(n)$ (up to lower-order factors), the power of $1/\varepsilon$ in the exponent cannot be lowered to any $\gamma(d-1)$ with $\gamma<1$, in every fixed dimension $d\ge2$.
--
--   **Formalization Note** The algorithms are `TimedNetworkScheme d γ` and `TimedValueScheme d γ`: one machine with $\varepsilon$ in its input and constants $C$, $p$ fixed before $\varepsilon$ and the instance; the time bound is $\lceil 2^{C(1/\varepsilon)^{\gamma(d-1)}}(\ell+2)^p\rceil$ steps. Weak ETH is `WeakETH`.
--
--   Differences from the source:
--   - reading: running time 2^{O(ε^{−γ(d−1)})} poly(n) → constants C ∈ ℝ and p ∈ ℕ with every run on (ε, t) within ⌈2^{C (1/ε)^{γ(d−1)}} · (ℓ + 2)^p⌉ steps; reason: the usual meaning of the O(·) and poly bounds; a constant factor and an additive constant in the exponent are absorbed by (ℓ + 2)^p since ℓ + 2 ≥ 2.
--   - reading: "(1 + ε)-approximation algorithm" → one machine taking ε as part of its input, with network output or with value output (both ruled out); reason: the proof (§6.2, §7.5) runs the algorithm with an ε computed from the instance.
--   - generalization: poly(n), n the number of terminals → polynomial in the input length ℓ; reason: ℓ ≥ n, so the time budget is larger and more algorithms are ruled out.
--   - generalization: correct for every ε > 0 and every point set in ℝ^d → only for rational ε ∈ (0, 1) and n ≥ 2 distinct rational points; reason: a weaker correctness requirement rules out more algorithms, and a source algorithm restricts to these inputs.
--   - reading: Hypothesis 1 "formulas of size n" → the length of the published binary code RevRedSAT.encCNF of a CNF formula of width ≤ 3, with a constant factor c in the time bound; reason: the usual meaning; with γ ranging over the open set (−∞, 1) the constant changes nothing.
--   - encoding: algorithms → Mathlib TM2 machines with finite stack alphabets, time counted by HMBinPacking.OutputsWithin; reason: Lean convention shared with the published machine model.
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Theorem 3 and Hypothesis 1, p.2 (PDF p.4); proofs §6.2, p.25 (PDF p.27) and §7.5, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_SteinerAPX_Supplement_WeakETH
import Definitions.Def_SteinerAPX_Supplement_TimedNetworkScheme

set_option autoImplicit false

namespace SteinerAPX.Supplement

/-- **Theorem 3 (under weak ETH, no `(1+ε)`-approximation in time `2^{O(ε^{−γ(d−1)})} poly(n)` in
`ℝ^d`).** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission
(manuscript sha256 6f78a9ea…), Theorem 3, p.2 (PDF p.4): "Under weak ETH, for every fixed d ≥ 2
and every constant γ < 1, Euclidean Steiner Tree in R^d admits no (1 + ε)-approximation algorithm
running in time 2^{O(ε^{−γ(d−1)})} poly(n)." Proofs: §6.2, p.25 (PDF p.27) for `d ≥ 3`, §7.5,
p.32 (PDF p.34) for `d = 2`.

If Hypothesis 1 (weak ETH) holds then, for every `d ≥ 2` and every real `γ < 1`, there is no
machine with constants `C`, `p` that, on input a rational `ε ∈ (0, 1)` and `n ≥ 2` distinct rational
points in `ℝ^d`, outputs a spanning network of length at most `(1 + ε) · OPT` within
`2^{C · ε^{−γ(d−1)}} · (ℓ + 2)^p` steps (`ℓ` the input length); and there is none that outputs a
rational `v` with `OPT ≤ v ≤ (1 + ε) · OPT` within that time.

**Formalization Note** The algorithm is one machine taking `ε` as part of its input; `C` and `p`
do not depend on `ε` or the instance. See `TimedNetworkScheme` for the time bound and why it is
taken in the input length. `γ` ranges over all reals below `1`, as on the page. -/
theorem theorem_3 (hETH : WeakETH) :
    ∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, γ < 1 →
      IsEmpty (TimedNetworkScheme d γ) ∧ IsEmpty (TimedValueScheme d γ) := by sorry

end SteinerAPX.Supplement
