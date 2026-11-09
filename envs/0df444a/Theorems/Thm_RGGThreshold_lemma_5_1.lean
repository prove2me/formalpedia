-- Prove2me | Theorems.Thm_RGGThreshold_lemma_5_1
-- name    : RGGThreshold.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:36.407491+00:00
-- url     : https://prove2.me/theorems/32a357b0-aace-4c8d-a6b6-dd572c71f12a
-- title:
--   Lemma 5.1 — the induction statement
-- statement:
--   Assume the standing hypotheses ($H\in\mathcal E(K^{\mathcal E})$, $1/3\ge p\ge n^{-1/3}(\log n)^A$, $d\ge Cn^2p(\log n)^A$, $\mathbb P[\langle x_1,x_2\rangle\ge\tau]=p$). Then for every $0\le s\le n-1$, almost surely,
--
--   $$
--   \mathbb P\big[G(n,d,p)|_{[s+1,n]}=H_s\wedge\mathcal F\,\big|\,\mathcal G_s\big]\le\prod_{s<i<j\le n}\Phi_{sij}\,\exp\Big(Z_s+\frac{\kappa_\triangle N_\triangle(H_s)}{\sqrt d}+\frac{\kappa_\square N_\square(H_s)}{d}+\frac{\kappa_\diamond N_\diamond(H_s)}{d}+\tilde O\big((n-s)R_{n,d,p}\big)\Big),
--   $$
--
--   where $H_s$ is the subgraph of $H$ induced by $\{s+1,\dots,n\}$. At $s=0$ this is Proposition 2.1.
--
--   **Formalization Note** The constants are quantified as $\exists A,\ \forall K^{\mathcal E}>0,\ \exists C>0,\ \exists C',B,N$, then $n\ge N$ and the rest; $\tilde O(X)$ is $C'(\log(nd))^BX$. The conditional probability is the conditional expectation of the indicator of $\{G|_{[s+1,n]}=H_s\}\cap\mathcal F$ given $\mathcal G_s$.
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
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 5.1, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_RGGThreshold_InE
import Definitions.Def_RGGThreshold_eventF
import Definitions.Def_RGGThreshold_PhiS
import Definitions.Def_RGGThreshold_kappaTri
import Definitions.Def_RGGThreshold_signedTri
import Definitions.Def_RGGThreshold_agreeCol

open MeasureTheory

namespace RGGThreshold

/-- **Lemma 5.1 (Induction statement)** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 5.1, pp.14–15 (PDF pp.16–17)). Assume
`H ∈ 𝓔`. Then for every `0 ≤ s ≤ n - 1`,
`P[G(n, d, p)|_{[s+1,n]} = H_s ∧ 𝓕 | 𝒢_s] ≤ ∏_{s<i<j≤n} Φ_{sij} exp(Z_s + κ_△N_△(H_s)/√d + κ_□N_□(H_s)/d
+ κ_◇N_◇(H_s)/d + Õ((n - s)R_{n,d,p}))`, where `H_s` is the subgraph of `H` induced by `{s+1, …, n}`.

**Formalization Note** The standing hypotheses (Proposition 2.1; §5, p.14: "the hypotheses of Proposition 2.1 remain
in force") are read with the quantifier order `∃ A, ∀ K^𝓔 > 0, ∃ C > 0`, then the `Õ`-constants
`C', B` and the threshold `N` for "large `n`", then `n, p, d, τ, H` and the rest. `Õ(X)` is
`C' (log(nd))^B X`; the threshold `c_{p,d}/√d` is any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p` (`capProb`). `s` is the paper index (0-based vertices `{i | s ≤ i}` are
the paper's `{s+1, …, n}`); `𝒢_s` is `revealedSigma n d s`. The conditional probability is the
`condExp` of the indicator of `{G|_{[s+1,n]} = H_s} ∩ 𝓕`, bounded almost everywhere. -/
theorem lemma_5_1 :
    ∃ A : ℕ, ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ (C' : ℝ) (B N : ℕ),
    ∀ n : ℕ, N ≤ n → ∀ p : ℝ, (n : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log n ^ A ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 2 * p * Real.log n ^ A ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    ∀ H : SimpleGraph (Fin n), InE K n p H →
    ∀ s : ℕ, s < n →
    ∀ᵐ x ∂(RGGDetect.prior n d),
      (RGGDetect.prior n d)[(agreeTail d τ H s ∩ eventF n d).indicator (fun _ => (1 : ℝ)) |
          revealedSigma n d s] x ≤
        prodPhi p d H s (gsCoord x) * Real.exp (Zs p H s (gsCoord x) +
          kappaTri p * signedTri p H (tailSet n s) / Real.sqrt d +
          kappaC4 p * signedC4 p H (tailSet n s) / d +
          kappaDia p * signedDia p H (tailSet n s) / d +
          C' * Real.log ((n : ℝ) * d) ^ B * (((n : ℝ) - s) * Rerr n d p)) := by sorry

end RGGThreshold
