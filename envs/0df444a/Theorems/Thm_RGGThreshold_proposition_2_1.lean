-- Prove2me | Theorems.Thm_RGGThreshold_proposition_2_1
-- name    : RGGThreshold.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:39.78921+00:00
-- url     : https://prove2.me/theorems/4871473b-2cdf-4cc1-bb7d-8a4566879f58
-- title:
--   Proposition 2.1 — $\mathbb P[G(n,d,p)=H\wedge\mathcal F]$ versus $\mathbb P[G(n,p)=H]$
-- statement:
--   For every constant $K^{\mathcal E}>0$ there is a constant $C$ and a large absolute constant $A$ such that the following holds. Let $H\in\mathcal E$ be a fixed graph on $[n]$, let $1/3\ge p\ge n^{-1/3}(\log n)^A$ and $d\ge Cn^2p(\log n)^A$. Then
--
--   $$
--   \mathbb P\big[G(n,d,p)=H\wedge\mathcal F\big]\le p^{e(H)}(1-p)^{\binom n2-e(H)}\exp\Big(\frac{\kappa_\triangle N_\triangle(H)}{\sqrt d}+\frac{\kappa_\square N_\square(H)}{d}+\frac{\kappa_\diamond N_\diamond(H)}{d}+\tilde O\big(nR_{n,d,p}\big)\Big).
--   $$
--
--   This is the main technical result of the paper: the probability that the random geometric graph realizes a pseudorandom graph $H$ exceeds its $G(n,p)$ probability by at most the signed-count corrections, and it holds well below the distinguishability threshold.
--
--   **Formalization Note** The probability is over $x_1,\dots,x_n$ independent uniform on $\mathbb S^{d-1}$; $p^{e(H)}(1-p)^{\binom n2-e(H)}$ is the published `RGGDetect.erWeight`. The constants are quantified as $\exists A,\ \forall K^{\mathcal E}>0,\ \exists C>0,\ \exists C',B,N$, then $n\ge N$ and the rest; $\tilde O(X)$ is $C'(\log(nd))^BX$.
--
--   Differences from the source:
--
--   - reading: "for every constant K^𝓔 > 0, there is a constant C and a large absolute constant A" → ∃ A, ∀ K > 0, ∃ C > 0; reason: A is absolute, so it does not depend on K^𝓔; this is the stronger of the two orders
--   - reading: Õ(X) ("constant-power logarithmic terms depending on n, p and d", §4.1) → C'·(log(nd))^B·X with C', B chosen after K and C and before n, p, d, H and the data; reason: uniform constants are what §4.1 allows; log(1/p) ≤ log n on the range p ≥ n^{-1/3}
--   - reading: the asymptotic statement holds for large n → ∃ N, ∀ n ≥ N after the constants; reason: "n large" made explicit
--   - encoding: A a large absolute (real) constant → A : ℕ, used as (log n)^A; reason: for n ≥ 3, raising A to ⌈A⌉ only shrinks the p-range, so the two forms are equivalent
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Proposition 2.1, eq. (4), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_RGGDetect_erLaw
import Definitions.Def_RGGThreshold_InE
import Definitions.Def_RGGThreshold_eventF
import Definitions.Def_RGGThreshold_kappaTri
import Definitions.Def_RGGThreshold_signedTri

open MeasureTheory

namespace RGGThreshold

/-- **Proposition 2.1** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Proposition 2.1, eq. (4), p.5 (PDF p.7)). For every constant
`K^𝓔 > 0` there is a constant `C` and a large absolute constant `A` such that: if `H ∈ 𝓔` is a fixed
graph on `[n]`, `1/3 ≥ p ≥ n^{-1/3}(log n)^A` and `d ≥ C n²p(log n)^A`, then
`P[G(n, d, p) = H ∧ 𝓕] ≤ p^{e(H)}(1-p)^{C(n,2)-e(H)} exp(κ_△N_△(H)/√d + κ_□N_□(H)/d + κ_◇N_◇(H)/d + Õ(nR_{n,d,p}))`.

**Formalization Note** The standing hypotheses (Proposition 2.1; §5, p.14: "the hypotheses of Proposition 2.1 remain
in force") are read with the quantifier order `∃ A, ∀ K^𝓔 > 0, ∃ C > 0`, then the `Õ`-constants
`C', B` and the threshold `N` for "large `n`", then `n, p, d, τ, H` and the rest. `Õ(X)` is
`C' (log(nd))^B X`; the threshold `c_{p,d}/√d` is any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p` (`capProb`). The probability is over `x_1, …, x_n` independent uniform on
`S^{d-1}` (`RGGDetect.prior`), `G(n, d, p) = H` is `rggGraph τ x = H`, and
`p^{e(H)}(1-p)^{C(n,2)-e(H)}` is `RGGDetect.erWeight p H`. -/
theorem proposition_2_1 :
    ∃ A : ℕ, ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ (C' : ℝ) (B N : ℕ),
    ∀ n : ℕ, N ≤ n → ∀ p : ℝ, (n : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log n ^ A ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 2 * p * Real.log n ^ A ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    ∀ H : SimpleGraph (Fin n), InE K n p H →
    (RGGDetect.prior n d).real {x | RGGDetect.rggGraph τ x = H ∧ x ∈ eventF n d} ≤
      RGGDetect.erWeight p H * Real.exp (
        kappaTri p * signedTri p H Finset.univ / Real.sqrt d +
        kappaC4 p * signedC4 p H Finset.univ / d +
        kappaDia p * signedDia p H Finset.univ / d +
        C' * Real.log ((n : ℝ) * d) ^ B * ((n : ℝ) * Rerr n d p)) := by sorry

end RGGThreshold
