-- Prove2me | Theorems.Thm_RGGThreshold_lemma_5_2
-- name    : RGGThreshold.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:56.507657+00:00
-- url     : https://prove2.me/theorems/0f9439f7-2211-4f26-a001-1e62770a1506
-- title:
--   Lemma 5.2 — edges at vertex $s$: conditional probability and conditional law (Setup (⋆))
-- statement:
--   Assume the standing hypotheses: $H\in\mathcal E(K^{\mathcal E})$, $1/3\ge p\ge n^{-1/3}(\log n)^A$, $d\ge Cn^2p(\log n)^A$, and the threshold has $\mathbb P[\langle x_1,x_2\rangle\ge\tau]=p$. Let $x_1,\dots,x_n$ be independent uniform on $\mathbb S^{d-1}$ with Gram–Schmidt coordinates $v_i(j)$, let $G$ be the random geometric graph, and let $1\le s<n$. Suppose the coordinates revealed in $\mathcal G_{s-1}$ satisfy $\Pi_{s-1}$. Then:
--
--   1. $$\mathbb P\big[si\in E(G)\iff si\in E(H)\ \text{for all } i\in\{s+1,\dots,n\}\,\big|\,\mathcal G_{s-1}\big]\le e^{\tilde O(n^{3/2}p^{1/2}/d)}\prod_{s<i\le n}\Phi_{s-1,s,i};$$
--   2. conditionally on $\mathcal G_{s-1}$ and on this agreement event, the coordinates $v_{s+1}(s),\dots,v_n(s)$ have the law of Setup (⋆).
--
--   Here $\Phi_{s-1,s,i}$ is $\Phi_{s-1,ij}$ at $(i,j)=(s,i)$. This is the one-step estimate of the vertex-exposure induction.
--
--   **Formalization Note** The constants are quantified as $\exists A,\ \forall K^{\mathcal E}>0,\ \exists C>0,\ \exists C',B,N$, then $n\ge N$, $p$, $d$, $\tau$, $H$, $s$; $\tilde O(X)$ is $C'(\log(nd))^BX$. Both clauses hold almost everywhere on $\Pi_{s-1}$. Conditional probabilities are conditional expectations of indicators given $\mathcal G_{s-1}$. Clause 2 is stated as: for every measurable set $S$ of columns, the conditional probability of "agreement and column in $S$" equals the conditional probability of agreement times the Setup (⋆) probability of $S$. The paper's vertex $s$ is the 0-based vertex $v$ with $v+1<n$.
--
--   Differences from the source:
--
--   - reading: "for every constant K^𝓔 > 0, there is a constant C and a large absolute constant A" → ∃ A, ∀ K > 0, ∃ C > 0; reason: A is absolute, so it does not depend on K^𝓔; this is the stronger of the two orders
--   - reading: Õ(X) ("constant-power logarithmic terms depending on n, p and d", §4.1) → C'·(log(nd))^B·X with C', B chosen after K and C and before n, p, d, H and the data; reason: uniform constants are what §4.1 allows; log(1/p) ≤ log n on the range p ≥ n^{-1/3}
--   - reading: the asymptotic statement holds for large n → ∃ N, ∀ n ≥ N after the constants; reason: "n large" made explicit
--   - encoding: A a large absolute (real) constant → A : ℕ, used as (log n)^A; reason: for n ≥ 3, raising A to ⌈A⌉ only shrinks the p-range, so the two forms are equivalent
--   - encoding: the conditional law of the column given 𝒢_{s−1} and the agreement event → E[1_{agree}1_{col∈S} | 𝒢_{s−1}] = E[1_{agree} | 𝒢_{s−1}]·Setup(⋆)(S) a.e. on Π_{s−1}, for every measurable S; reason: this identity is the definition of the conditional law given 𝒢_{s−1} and an event
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 5.2 and Setup (⋆), pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_RGGThreshold_InE
import Definitions.Def_RGGThreshold_eventF
import Definitions.Def_RGGThreshold_PhiS
import Definitions.Def_RGGThreshold_setupStar
import Definitions.Def_RGGThreshold_agreeCol

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 5.2** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 5.2 and Setup (⋆), pp.15–16 (PDF pp.17–18)). Let `1 ≤ s < n` and
`H ∈ 𝓔`. Let `x_1, …, x_n` be independent uniform on `S^{d-1}` with Gram–Schmidt coordinates
`v_i(j)` and random geometric graph `G`. On the event `Π_{s-1}` for the revealed coordinates
`𝒢_{s-1}` (`v_i(j)`, `j ≤ s-1`):

(a) `P[si ∈ E(G) ⇔ si ∈ E(H) for all i ∈ {s+1, …, n} | 𝒢_{s-1}] ≤ e^{Õ(n^{3/2}p^{1/2}/d)} ∏_{s<i≤n} Φ_{s-1,s,i}`;

(b) conditionally on `𝒢_{s-1}` and on that agreement event, the column `v_{s+1}(s), …, v_n(s)` has
the law of Setup (⋆).

**Formalization Note** The standing hypotheses (Proposition 2.1; §5, p.14: "the hypotheses of Proposition 2.1 remain
in force") are read with the quantifier order `∃ A, ∀ K^𝓔 > 0, ∃ C > 0`, then the `Õ`-constants
`C', B` and the threshold `N` for "large `n`", then `n, p, d, τ, H` and the rest. `Õ(X)` is
`C' (log(nd))^B X`; the threshold `c_{p,d}/√d` is any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p` (`capProb`). The paper's vertex `s` is the 0-based vertex `v`
(`s = v + 1`, `1 ≤ s < n` is `v + 1 < n`); `𝒢_{s-1}` is `revealedSigma n d v`, `Π_{s-1}` is
`projW d v`, `Φ_{s-1,s,i}` is `PhiS p d H v W v i`. Conditional probabilities are `condExp` of
indicators; (b) states, for every measurable set `S` of columns, that the conditional probability of
"agreement and column in `S`" is the conditional probability of agreement times the Setup (⋆)
probability of `S`, which says that the conditional law given `𝒢_{s-1}` and agreement is Setup (⋆). -/
theorem lemma_5_2 :
    ∃ A : ℕ, ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ (C' : ℝ) (B N : ℕ),
    ∀ n : ℕ, N ≤ n → ∀ p : ℝ, (n : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log n ^ A ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 2 * p * Real.log n ^ A ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    ∀ H : SimpleGraph (Fin n), InE K n p H →
    ∀ v : Fin n, v.val + 1 < n →
    (∀ᵐ x ∂(RGGDetect.prior n d), projW d v.val (gsCoord x) →
      (RGGDetect.prior n d)[(agreeCol d τ H v).indicator (fun _ => (1 : ℝ)) |
          revealedSigma n d v.val] x ≤
        Real.exp (C' * Real.log ((n : ℝ) * d) ^ B * ((n : ℝ) ^ (3 / 2 : ℝ) * p ^ (1 / 2 : ℝ) / d)) *
          ∏ i : Fin n, if v < i then PhiS p d H v.val (gsCoord x) v i else 1) ∧
    (∀ S : Set (Fin n → ℝ), MeasurableSet S →
      ∀ᵐ x ∂(RGGDetect.prior n d), projW d v.val (gsCoord x) →
        (RGGDetect.prior n d)[(agreeCol d τ H v ∩ colMap v ⁻¹' S).indicator (fun _ => (1 : ℝ)) |
            revealedSigma n d v.val] x =
          (RGGDetect.prior n d)[(agreeCol d τ H v).indicator (fun _ => (1 : ℝ)) |
            revealedSigma n d v.val] x * (setupStar d τ H v (gsCoord x)).real S) := by sorry

end RGGThreshold
