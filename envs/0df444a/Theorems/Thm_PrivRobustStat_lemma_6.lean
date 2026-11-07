-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_6
-- name    : PrivRobustStat.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:02.073199+00:00
-- url     : https://prove2.me/theorems/0d589ffd-6d29-4ab0-85c2-9d5d479d586d
-- title:
--   Lemma 6, p.19 (corrected: $p=\lceil\log_2(2d)\rceil$) — with probability $1-\beta/2$ the replayed sketches satisfy (15) and the noise satisfies (16)
-- statement:
--   **Lemma 6** (utility of PrivateScores). There is a universal constant $C>0$ such that, running Algorithm 3 with $r=\lceil C\log((n+d)/\beta)\rceil$ on any $x_{[n]}$ with $n\ge1$, centre $c$, $w\in[0,\tfrac1n]^n$, $\kappa,\tau_{\max}>0$, $\beta\in(0,1)$ and the depth $p=\lceil\log_2(2d)\rceil$ of Algorithm 1, with $\Gamma_0=I$ and $\Gamma_j=\hat\Sigma(w^{(j)})\Gamma_{j-1}\hat\Sigma(w^{(j)})+r\sigma_j^2I$ as in (14), with probability at least $1-\beta/2$ simultaneously:
--
--   1. for every $k\in[0,p]$, $j\in[0,k]$ and $N\in\{I\}\cup\{M_1,\dots,M_n\}$,
--   $$\tfrac9{10}\operatorname{Tr}(N\Gamma_j)\le\operatorname{Tr}(Z_{k,j}^\top NZ_{k,j})\le\tfrac{11}{10}\operatorname{Tr}(N\Gamma_j);\tag{15}$$
--   2. for every $j\in[p]$, $\ d\,r\,\sigma_j^2\le\frac{\kappa^2}{128p}\operatorname{Tr}(\Gamma_{j-1})$. (16)
--
--   The replayed sketches thus track the noiseless power iteration, which is what lets the scores certify a potential decrease.
--
--   **Formalization Note** $\Gamma_j$ and $\sigma_j$ depend on the run through $w^{(j)}$ and $\omega_j$; they are computed from the same Gaussian draws as the sketches, and (15)–(16) hold on one measurable event.
--
--   Differences from the source:
--   - encoding: Γ_j as in (14), σ_j of Algorithm 3 → computed from the same run (same Gaussian draws) as the sketches Z_{k,j}; reason: Γ_j and σ_j are random; the lemma is a statement about one run
--   - correction: p (an input of Algorithm 3) → p = ⌈log₂(2d)⌉, as in Algorithm 1, Line 1; reason: the proof's union bound O((n+1)p²e^{−cr}) ≤ β/2 ties p to n and d, and Algorithm 1 is the only caller; for arbitrary p the p + 1 independent sketches Z_{k,0} eventually violate (15) at fixed r
--   - reading: β and n (no range stated) → β ∈ (0, 1), n ≥ 1; reason: β is a failure probability, and n ≥ 1 is the paper's standing case; at n = 0, d = 1, β near 1 the printed r is 1 and (15) fails
--   - encoding: "for a universal constant C > 0" → ∃ C > 0 before every other quantity; reason: meaning of a universal constant
--   - encoding: with probability at least 1 − β → a measurable event of the Gaussian draws with that probability; reason: avoids outer measure; same claim
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 6, p.19 (PDF p.22); (14), p.19; Algorithm 3, p.18

import Mathlib
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 6** (utility of `PrivateScores`), p.19 (PDF p.22); Γ_j as in (14), p.19.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Run Algorithm 3 with r = ⌈C log((n+d)/β)⌉, for a universal constant C > 0, and define Γ_j as in
(14). With probability at least 1 − β/2, the following hold simultaneously. (1) (Sketch estimates)
For every k ∈ [0, p], j ∈ [0, k] and N ∈ {I} ∪ M[n], 9/10 Tr(NΓ_j) ≤ Tr(Z⊤_{k,j}NZ_{k,j}) ≤
11/10 Tr(NΓ_j). (15) (2) (Noise bound) For every j ∈ [p], drσ_j² ≤ κ²/(128p) Tr(Γ_{j−1}). (16)"

(14): `Γ₀ := I`, `Γ_j := Σ̂(w^(j))Γ_{j−1}Σ̂(w^(j)) + rσ_j²I` for `j ∈ [p]`.

**Formalization Note.** `C` is chosen before everything else. Algorithm 3's inputs: any dataset
`x[n]` with `n ≥ 1`, public centre `c`, `w ∈ [0, 1/n]^n`, `κ, τ_max > 0`, `β ∈ (0, 1)`,
`r = rDim C n d β`, and the depth `p = ⌈log₂(2d)⌉` of Algorithm 1 (`pDepth d`). The proof's union bound
`O((n+1)p²e^{−cr}) ≤ β/2` needs `p` tied to `n, d`: for an arbitrary `p` the `p + 1` independent sketches
`Z_{k,0}` eventually violate (15) at `r` fixed. `n ≥ 1` gives `log((n+d)/β) ≥ log 2`; at `n = 0`, `d = 1`,
`β` near `1` the printed `r` is `1` and (15) fails.
`Γ_j` and `σ_j` depend on the run (through `w^(j)` and `ω_j`): `a3Gamma` and `a3sigma` are computed
from the same draws `g` as the sketches `Z_{k,j}` (`a3sketch`), and (15)–(16) hold pointwise on one
measurable event of probability `≥ 1 − β/2`. -/
theorem lemma_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ), InBox n w →
        1 ≤ n → ∀ (κ τmax β : ℝ), 0 < κ → 0 < τmax → 0 < β → β < 1 →
          ∃ E : Set (ℕ × ℕ × Fin d × Fin (rDim C n d β) → ℝ), MeasurableSet E ∧
            ENNReal.ofReal (1 - β / 2) ≤ stdGauss (ℕ × ℕ × Fin d × Fin (rDim C n d β)) E ∧
            ∀ g ∈ E,
              (∀ k ≤ pDepth d, ∀ j ≤ k, ∀ N : Matrix (Fin d) (Fin d) ℝ,
                (N = 1 ∨ ∃ i, N = outer (x i - c)) →
                9 / 10 * Matrix.trace (N * a3Gamma x c w κ τmax (pDepth d) g j) ≤
                    quadTr (a3sketch x c w κ τmax (pDepth d) g k j) N ∧
                  quadTr (a3sketch x c w κ τmax (pDepth d) g k j) N ≤
                    11 / 10 * Matrix.trace (N * a3Gamma x c w κ τmax (pDepth d) g j)) ∧
              ∀ j ∈ Finset.Icc 1 (pDepth d),
                (d : ℝ) * (rDim C n d β : ℝ) * a3sigma x c w κ τmax (pDepth d) g j ^ 2 ≤
                  κ ^ 2 / (128 * (pDepth d : ℝ)) * Matrix.trace (a3Gamma x c w κ τmax (pDepth d) g (j - 1)) := by sorry

end PrivRobustStat
