-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_5
-- name    : SublinearSteiner.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:16.074892+00:00
-- url     : https://prove2.me/theorems/ee06d018-ed75-4bdf-a5c8-39017768e1fd
-- title:
--   Lemma 4.5 — independent terminal covers, (4.6), (4.7)
-- statement:
--   Let $k=|T|\ge1$, $0<\beta<1$, $I\ge1$, and let $a_i>0$ be scales. Retain terminals as in the retention law, with $\rho_i=\delta a_i$. Except with probability $\beta$, simultaneously at all scales, $N_i$ is a $\rho_i$-cover of $T$ and
--   $$g_i\le H_c+\frac{4\psi hL}{\delta a_i},\qquad H_c=2+2\psi+\log(2I/\beta).$$
--   Moreover, for every adaptive procedure that does not observe unresolved draws, the total number $W$ of draws and the number $A$ of retained terminals it has found satisfy
--   $$\mathbb P\bigl[W>2k(A+\log(1/\beta))\text{ at some time}\bigr]\le\beta.$$
--
--   The two parts bound the size of the random covers, and bound the cost of resolving their bits by the number of retained terminals found.
--
--   Differences from the source:
--   - generalization: (4.7) with the β, ψ and r_c of the covers → (4.7) for every β_W ∈ (0,1), every ψ′ and all radii; reason: the proof does not use them, and Corollary 4.6 applies (4.7) with a β of its own
--   - generalization: the scales of the grid (4.2) → any positive scales; reason: the proof uses only a_i > 0
--   - reading: every adaptive procedure that does not observe unresolved draws → a strategy choosing the next pair from the completed resolutions and their draws, testing the inequality after every draw; reason: the page’s notion; a randomized procedure is a mixture of strategies
--   - encoding: unbounded private streams → streams of every finite horizon H; reason: the event at infinite horizon is the increasing limit of the finite ones
--   - generalization: the floored metric of p.19 ("From now on we work with the floored metric") → any metric w on Fin n, with its own L and OPT; reason: the proof uses no property of the flooring; the floored metric is a metric (SublinearSteiner.floored), so the statement specializes to it
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.5, (4.6), (4.7), p.23, with the setting of p.22

import Mathlib
import Definitions.Def_SublinearSteiner_Retention
import Definitions.Def_SublinearSteiner_Statistics

open scoped Classical

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.5 (Covers), (4.6), (4.7), p.23. Except with probability `β`, simultaneously at all scales, `N_i` is a
`ρ_i`-cover of `T` and `g_i ≤ H_c + 4ψhL/(δa_i)`, `H_c = 2 + 2ψ + log(2I/β)`. Moreover, for every adaptive procedure that does
not observe unresolved draws, the total number `W` of draws and the number `A` of retained terminals it has found satisfy
`P[W > 2k(A + log(1/β)) at some time] ≤ β`.

**Formalization Note.**
* (4.6) is about the product law of the retention bits, with `ρ_i = δa_i`, `h`, `ψ` and `r_c = ρ_i/h` as on p.22.
* (4.7) is stated for every strategy, every finite horizon `H` of the private streams, and every `β_W ∈ (0, 1)`, `ψ'` and radii
  `r`. It does not depend on the choice of radii or `ψ`, and Corollary 4.6 applies it with a `β` of its own.
* `t` ranges over all step counts, and the inequality is tested after every draw. -/
theorem lemma_4_5 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (hk : 1 ≤ T.card) (L : ℝ)
    (hL : IsTerminalMST T w L) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (I : ℕ) (hI : 1 ≤ I)
    (a : Fin I → ℝ) (ha : ∀ i, 0 < a i) (x₀ : Fin n) (hx₀ : x₀ ∈ T) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Bits T I =>
        ¬ ∀ i, IsCover w T (retainedSet x₀ ω i) (delta * a i) ∧
          ((retainedSet x₀ ω i).card : ℝ) ≤
            coverHc (psiBound T.card I β) I β +
              4 * psiBound T.card I β * hopBound T.card * L / (delta * a i)),
      bitsWeight (scaleRetention w T a (psiBound T.card I β) (hopBound T.card)) ω) ≤ β ∧
    (∀ (βW : ℝ), 0 < βW → βW < 1 → ∀ (ψ' H : ℕ) (r : Fin I → ℝ) (σ : DrawStrategy T I),
      ((Finset.univ.filter (fun ω : DrawStream T I H =>
          ∃ t : ℕ, (((drawRun w r ψ' σ ω t).draws : ℕ) : ℝ) >
            2 * T.card * (((drawRun w r ψ' σ ω t).found : ℕ) + Real.log (1 / βW)))).card : ℝ)
        ≤ βW * (Fintype.card (DrawStream T I H) : ℝ)) := by sorry

end SublinearSteiner
