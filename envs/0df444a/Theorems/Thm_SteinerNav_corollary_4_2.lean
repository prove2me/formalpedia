-- Prove2me | Theorems.Thm_SteinerNav_corollary_4_2
-- name    : SteinerNav.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:54.560999+00:00
-- url     : https://prove2.me/theorems/aeb25e19-028f-4bbe-9da3-97aa646b57bd
-- title:
--   Corollary 4.2 — $K=\lceil C\log n\rceil$ samples per nonempty annulus give $O(L\log n)$ candidates that $\alpha$-cover $P\setminus\{s\}$ w.h.p.
-- statement:
--   For every $c>0$ there are constants $C,C'>0$ with the following property. Let $d\ge1$, $\alpha=1+1/d$, let $P\subset\mathbb R^d$ have $n\ge2$ points, let $L=1+\lfloor\log_2\Delta\rfloor$, fix a source $s\in P$, and set $K=\lceil C\ln n\rceil$. Draw independent uniformly random unit vectors $u_{i,j}$, $i<L$, $j<K$, and let the candidates be the points $s+2^i\sigma\sqrt{2\varepsilon}\,u_{i,j}$ over $j<K$ and the indices $i$ whose annulus contains a target. Then:
--
--   1. $KL\le C'\,L\ln n$, that is, $KL=O(L\log n)$;
--   2. on every outcome there are at most $KL$ candidates;
--   3. with probability at least $1-n^{-c}$, the candidates strictly $\alpha$-cover $P\setminus\{s\}$ with respect to $s$:
--   $$\Pr\big[\forall t\in P\setminus\{s\}\ \exists \text{ candidate } v:\ \|v-t\|<\|s-t\|/\alpha\big]\ \ge\ 1-n^{-c}.$$
--
--   A sampled location already in $P$ can be used as an input neighbor and the others are added as Steiner points; that split is made by the construction of Theorem 3.
--
--   **Formalization Note** "With high probability" is the paper's (§3, p.5): probability at least $1-n^{-c}$ with $c>0$ as large as desired, hence "for every $c$ there is $C$". Logarithms are natural; another fixed base changes only $C$ and $C'$. The samples are indexed by $(i,j)\in\{0,\dots,L-1\}\times\{0,\dots,K-1\}$ under the product of `uniformSphere d`; samples drawn for an empty annulus are unused.
--
--   Differences from the source:
--   - reading: "with high probability" → for every c > 0 there is C with probability ≥ 1 − n^(−c); reason: the paper's own definition, §3, p.5.
--   - encoding: sampling only in nonempty annuli → L·K i.i.d. vectors indexed by Fin L × Fin K, those of empty annuli unused; reason: same law of the used samples.
--   - encoding: a boundary target belongs to one annulus → closed annuli, a boundary target makes both annuli nonempty; reason: only adds candidates; the count bound KL and the cover are unchanged.
--   - encoding: "a sampled location already in P can be used as an input neighbor; other sampled locations are added as Steiner points" → not part of this item; reason: it prescribes how candidates are used, implemented by the construction (constructionEdges, R = S \ P) and asserted in the navigability milestone.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Corollary 4.2, p.7

import Mathlib
import Definitions.Def_SteinerNav_annularCandidates

namespace SteinerNav

open MeasureTheory RegretBandits.Nonlinear

/-- Corollary 4.2: for every exponent `c > 0` there is a constant `C` (and `C'` for the `O(L log n)`)
such that, for every `d ≥ 1`, `P` with `n = |P| ≥ 2`, source `s ∈ P`, `α = 1 + 1/d`, `K = ⌈C ln n⌉`, `L = 1 +
⌊log₂ Δ⌋`, sampling i.i.d. uniform unit vectors `u i j` gives at most `KL = O(L log n)` candidates on
every outcome, and they `α`-cover `P \ {s}` with respect to `s` with probability at least `1 − n^(−c)`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Corollary 4.2, p.7).

**Formalization Note** "With high probability" is the page's: `1 − n^(−c)` with `c` as large as desired
(§3, p.5), hence `∀ c, ∃ C`. Logarithms are natural; another fixed base only changes `C`. -/
theorem corollary_4_2 : ∀ c : ℝ, 0 < c → ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ P : Finset (Pt d), 2 ≤ P.card → ∀ s ∈ P,
      let α : ℝ := 1 + 1 / (d : ℝ)
      let n : ℝ := (P.card : ℝ)
      let K : ℕ := ⌈C * Real.log n⌉₊
      let L : ℕ := annulusCount P
      ((K : ℝ) * (L : ℝ) ≤ C' * ((L : ℝ) * Real.log n)) ∧
      (∀ u : Fin L × Fin K → Pt d, (annularCandidates α P s K L u).card ≤ K * L) ∧
      ENNReal.ofReal (1 - n ^ (-c)) ≤
        Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
          {u | CoversSet α s (annularCandidates α P s K L u) P} := by sorry

end SteinerNav
