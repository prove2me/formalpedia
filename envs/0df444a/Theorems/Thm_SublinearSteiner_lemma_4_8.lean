-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_8
-- name    : SublinearSteiner.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:01.733011+00:00
-- url     : https://prove2.me/theorems/ffa979c0-d2f2-48ac-9d11-7717006a7dc5
-- title:
--   Lemma 4.8 — deletion and scores, (4.13), (4.14)
-- statement:
--   Let $N\subseteq T$ be nonempty, $g=|N|$, $S$ a set of at most $s$ centers, $B$ an integer, and $\mathcal C_0$, $U$, $b_{\mathrm{large}}$, $\Psi_U$, $\Phi$ as defined at scale $a>0$. Then
--   $$\Phi\le b_{\mathrm{large}}+|\mathcal C_0|+\Psi_U,\qquad|\mathcal C_0|-2s+\Psi_U\le\Phi.$$
--   Suppose a graph on $U$ has expected random-greedy matching size $\mu$ with $\Psi_U/2-\Delta\le\mu\le\Psi_U$. Then the score of a uniform retained point lies in $[0,1]$ and has mean $(|\mathcal C_0|+\mu)/g$, and with $O(\xi^{-2}\log(2/\beta))$ samples one obtains, with probability at least $1-\beta$, a value $Z$ with $0\le Z\le\Phi$ and
--   $$Z\ge\Phi/2-b_{\mathrm{large}}/2-\Delta-2s-3\xi g.$$
--   Here $Z=\max\{0,g_-\max\{0,\hat\vartheta-\xi\}-2s\}$ for any $g_-$ with $(1-\xi)g\le g_-\le g$.
--
--   This is how the saving of a retained system is estimated by a local exploration.
--
--   Differences from the source:
--   - reading: a bounded score, a value Z → the explicit score and the explicit Z of the proof on p.25; reason: an abstract existential would make the clause empty
--   - reading: calibration events → any g₋ with (1 − ξ)g ≤ g₋ ≤ g; reason: this is what (4.8) provides
--   - generalization: O(ξ⁻² log(2/β)) samples → every number of samples at least C₀ ξ⁻² log(2/β), with C₀ universal; reason: it contains the sample size the page intends
--   - generalization: N the retained cover N_i at a grid scale of the floored metric → any nonempty N ⊆ T, any scale a > 0, any metric; reason: the proof of (4.13) and of the score uses neither the cover property nor the flooring; the retained cover is a nonempty subset of T (it contains the fixed terminal)
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.8, (4.13), (4.14), p.24, and its proof, p.25

import Mathlib
import Definitions.Def_SublinearSteiner_ScoreEstimator

open scoped Classical

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.8 (Deletion and scores), (4.13), (4.14), p.24. We have `Φ ≤ b_large + |C0| + Ψ_U` and `|C0| − 2s + Ψ_U ≤ Φ`. Suppose a
graph on `U` has expected random-greedy matching size `μ` with `Ψ_U/2 − Δ ≤ μ ≤ Ψ_U`. Then a bounded score of a uniform retained point has
mean `(|C0| + μ)/g`, and with `O(ξ⁻² log(2/β))` samples one obtains, with probability `1 − β`, a value `Z` with `0 ≤ Z ≤ Φ` and
`Z ≥ Φ/2 − b_large/2 − Δ − 2s − 3ξg`.

**Formalization Note.**
* The score and `Z` are the ones of the proof on p.25, not an abstract existential: `scoreValue`, `scoreEstimate`.
* The constant `C₀` of the `O` is universal, chosen before the system. Any number `N_s` of samples at least `C₀ ξ⁻² log(2/β)` works.
* `g₋` is any number with `(1 − ξ)g ≤ g₋ ≤ g`, from (4.8), which is what the proof's calibration event provides.
* The mean and the bound on the score do not need the bounds on `μ`. -/
theorem lemma_4_8 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (w : FinMetric n) (T N S : Finset (Fin n)) (a : ℝ) (s B : ℕ),
      0 < a → N ⊆ T → N.Nonempty → S.card ≤ s →
      ((coverSaving w N a : ℝ) ≤ largeCount w N a B + (hitComps w T N S a B).card +
          restrictedSaving w N a (restComps w T N S a B) ∧
        ((hitComps w T N S a B).card : ℝ) - 2 * s + restrictedSaving w N a (restComps w T N S a B)
          ≤ coverSaving w N a) ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (H : Multigraph ↥(restComps w T N S a B) E),
        (∀ x : ScoreSample N E, 0 ≤ scoreValue w T N S a B H x ∧ scoreValue w T N S a B H x ≤ 1) ∧
        (∑ x : ScoreSample N E, scoreWeight w N a x * scoreValue w T N S a B H x
          = (((hitComps w T N S a B).card : ℝ) + H.expectedMatching) / N.card) ∧
        ∀ Δ : ℝ, (restrictedSaving w N a (restComps w T N S a B) : ℝ) / 2 - Δ ≤ H.expectedMatching →
          H.expectedMatching ≤ restrictedSaving w N a (restComps w T N S a B) →
          ∀ (ξ β gm : ℝ) (Ns : ℕ), 0 < ξ → ξ < 1 → 0 < β → β < 1 →
            (1 - ξ) * N.card ≤ gm → gm ≤ N.card → C₀ * (ξ ^ 2)⁻¹ * Real.log (2 / β) ≤ Ns →
            1 - β ≤ ∑ smp ∈ Finset.univ.filter (fun smp : Fin Ns → ScoreSample N E =>
                let Z := scoreEstimate gm ξ s ((∑ j, scoreValue w T N S a B H (smp j)) / Ns)
                0 ≤ Z ∧ Z ≤ coverSaving w N a ∧
                  (coverSaving w N a : ℝ) / 2 - (largeCount w N a B : ℝ) / 2 - Δ - 2 * s
                    - 3 * ξ * N.card ≤ Z),
              ∏ j, scoreWeight w N a (smp j) := by sorry

end SublinearSteiner
