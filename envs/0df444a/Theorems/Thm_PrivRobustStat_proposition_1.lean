-- Prove2me | Theorems.Thm_PrivRobustStat_proposition_1
-- name    : PrivRobustStat.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:07.915178+00:00
-- url     : https://prove2.me/theorems/bd139ee7-80fe-4051-854a-4513924c3f55
-- title:
--   Proposition 1, p.16 — PrivateFastCovFilter decreases the potential to $\tfrac9{10}\Phi$ while losing little good weight
-- statement:
--   **Proposition 1** (utility of PrivateFastCovFilter). There is a universal constant $C>0$ (the constant of $r=\lceil C\log((n+d)/\beta)\rceil$ in Algorithm 1) such that the following holds. Let $x_{[n]}\subset\mathbb R^d$, $c\in\mathbb R^d$, $M_i=(x_i-c)(x_i-c)^\top$, $\hat\Sigma(u)=\sum_iu_iM_i$, and let $G\subseteq[n]$ with $|B|\le\alpha n$ for $B=[n]\setminus G$. Let $\alpha,\beta\in(0,\tfrac14)$, $\Phi>0$, $T\ge1$, $\kappa=\Phi^{1/q}$, and $w\in[0,\tfrac1n]^n$ with $\|w\|_1\ge1-2\alpha$ such that
--
--   (a) $\Psi(w)\le\Phi$, and (b) $\hat\Sigma(w_G)\preceq\frac{\kappa}{400}I$.
--
--   Then with probability at least $1-\beta$, Algorithm 1 returns $w'$ with $0_n\le w'\le w$ and
--
--   $$\Psi(w')\le\tfrac9{10}\Phi,\qquad \|[w-w']_G\|_1\le\frac{\alpha}{100T}+\tfrac12\|[w-w']_B\|_1 .$$
--
--   One filtering call thus shrinks the potential by a constant factor; Theorem 4 applies it $T$ times.
--
--   Differences from the source:
--   - reading: "Under Definition 1" → any dataset x[n], public centre c, and any G ⊆ [n] with |[n] ∖ G| ≤ αn; reason: the §3 analysis uses only these properties; the proof of Theorem 4 instantiates G := G₀
--   - encoding: T ∈ ℕ → T ≥ 1; reason: with T = 0, τ_max = 0, which Algorithm 3's input condition τ_max > 0 excludes
--   - encoding: "C > 0 is a universal constant, cf. Lemma 6" (Algorithm 1, Line 3) → ∃ C > 0 before every other quantity, used as r = ⌈C log((n + d)/β)⌉; reason: meaning of a universal constant
--   - encoding: Algorithm 1, Line 8 → PrivateSoftFilter by the binary search of the proof of Lemma 9; reason: the implementation of Section 3.3 that Proposition 1 refers to
--   - encoding: with probability at least 1 − β → a measurable event of the Gaussian draws with that probability; reason: avoids outer measure; same claim
--   - encoding: the running time (11) → not in this item; the mission goal theorem_4 bounds the work of a machine program; reason: the item states the algorithm as a random map of data and noise, which has no cost (planning decision 10)
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Proposition 1, p.16 (PDF p.19); proof in §3.4, pp.25–26

import Mathlib
import Definitions.Def_PrivRobustStat_Privacy
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Proposition 1** (utility of `PrivateFastCovFilter`), p.16 (PDF p.19); proof in §3.4, pp.25–26.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Under Definition 1, consider inputs w to Algorithm 1 with ∥w∥₁ ≥ 1 − 2α. Assume: (a) (Potential
bound) Ψ(w) ≤ Φ. (b) (Upper bound on the good aggregate) Σ̂(w_G) ⪯ κ/400 I. Then, with probability at
least 1 − β, Algorithm 1 returns weights w′ satisfying 0_n ≤ w′ ≤ w, and: (1) (Potential decrease)
Ψ(w′) ≤ 9/10 Φ. (2) (Good weight loss) ∥[w − w′]_G∥₁ ≤ α/(100T) + ½∥[w − w′]_B∥₁. Furthermore,
there exists an implementation (Section 3.3) which runs in time
O(nd log²(d) log((n+d)/β) + n log(T log(d)/α)). (11)"

**Formalization Note.**
* "Under Definition 1" in §3: any dataset `x[n]` with public centre `c`, and a set `G ⊆ [n]` with
  `|[n] \ G| ≤ αn`, `B := [n] \ G` (the proof of Theorem 4 uses `G := G₀`, p.35).
* `Σ̂(u) = ∑_i u_iM_i = covC x u c`, `Ψ = potential` (10), `κ = Φ^{1/q}`.
* Algorithm 1's inputs: `w ∈ [0, 1/n]^n`, `Φ > 0`, `T ∈ ℕ` with `T ≥ 1` (so `τ_max > 0`), and
  `α, β ∈ (0, 1/4)`. `C` is the universal constant of Algorithm 1, Line 3 (`r = ⌈C log((n+d)/β)⌉`),
  chosen before everything else; Algorithm 4 is the binary-search implementation (Line 8).
* The event is a measurable set of Gaussian draws of probability `≥ 1 − β`. The running time (11)
  is carried by the goal theorem's time clause. -/
theorem proposition_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d n : ℕ} (x : Fin n → Vec d) (c : Vec d) (G : Finset (Fin n)) (α β Φ : ℝ) (T : ℕ),
        0 < α → α < 1 / 4 → 0 < β → β < 1 / 4 → 0 < Φ → 1 ≤ T →
        ((Gᶜ).card : ℝ) ≤ α * n →
        ∀ w : Fin n → ℝ, InBox n w → 1 - 2 * α ≤ l1 w → potential x c w ≤ Φ →
          ((kappaOf d Φ / 400) • (1 : Matrix (Fin d) (Fin d) ℝ) - covC x (restrict w G) c).PosSemidef →
          ∃ E : Set (A1Idx d (rDim C n d β) → ℝ), MeasurableSet E ∧
            ENNReal.ofReal (1 - β) ≤ stdGauss (A1Idx d (rDim C n d β)) E ∧
            ∀ g ∈ E,
              (∀ i, 0 ≤ alg1 C x c w Φ T α β g i ∧ alg1 C x c w Φ T α β g i ≤ w i) ∧
              potential x c (alg1 C x c w Φ T α β g) ≤ 9 / 10 * Φ ∧
              l1 (restrict (w - alg1 C x c w Φ T α β g) G) ≤
                α / (100 * (T : ℝ)) + 1 / 2 * l1 (restrict (w - alg1 C x c w Φ T α β g) Gᶜ) := by sorry

end PrivRobustStat
