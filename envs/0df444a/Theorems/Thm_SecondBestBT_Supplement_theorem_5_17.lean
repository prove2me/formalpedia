-- Prove2me | Theorems.Thm_SecondBestBT_Supplement_theorem_5_17
-- name    : SecondBestBT.Supplement.theorem_5_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:40:26.898088+00:00
-- url     : https://prove2.me/theorems/de252d98-5930-40fc-9169-f44a77673ebf
-- title:
--   Theorem 5.17 — characterization of undominated states
-- statement:
--   Fix $\alpha>0$, $\beta=\tfrac12$, and an admissible global ratio vector $(0,r_1,\dots,r_k)$ with $k\ge1$ and $r_i<\infty$ for $1\le i\le k$. Write $\mathbf r=(r_1,\dots,r_k)$ and let $\omega^\star:=\mathrm{ALG}_2(\omega_0;\mathbf r)$. Then
--   $$
--   \omega^\star\text{ is undominated}\quad\Longleftrightarrow\quad
--   \begin{cases}
--   \omega^\star\in\mathcal S_{(0,\mathbf r)}\cup\mathcal S_{\mathbf r},\\[2pt]
--   \mathrm{ALG}_2(\omega_0;\mathbf r')\in\mathcal S_{(0,\mathbf r')}\ \text{ for every nonempty proper suffix } \mathbf r' \text{ of } \mathbf r.
--   \end{cases}
--   $$
--   Moreover, the first condition holds if and only if the terminal threshold of the canonical execution $\mathrm{ALG}_2(\omega_0;\mathbf r)$ is $0$ or $1$.
--
--   Here $\omega_0=(\beta/(1+\alpha);0)$ is the base clear state, $\mathrm{ALG}_2$ is the state-transition procedure (Algorithm 2) driven by the normalized residual $\hat H$ of Eq. (13), achievable states and suffix classes $\mathcal S$ are those of Definition 5.1 (states reached by Algorithm 1 for an $\alpha$-weakly regular full-support seller), and "undominated" refers to the dominance order of Definition 5.2 over all achievable states. The theorem identifies exactly when the canonical output of the greedy construction cannot be dominated by any achievable state.
--
--   Differences from the source:
--   - encoding: states $(y;r_t,\dots,r_m)$ with $r_i\in\mathbb R_{\ge0}\cup\{\infty\}$ → pairs of a real and a list of values in `ℝ≥0∞`; reason: the paper's notation records only the threshold allocation and the ratio values; same instances
--   - encoding: "$\omega^\star$ is undominated", "$\omega^\star\in\mathcal S$", "$\mathrm{ALG}_2(\omega_0;\mathbf r')\in\mathcal S$" → ALG2 returns an `Option`; each property is read as: the run does not fail and its output state has the property; reason: a failing run has no output state; by Lemma 5.11 ALG2 does not fail on admissible inputs, so the reading changes no instance
--   - encoding: line 7 "Solve $\hat H_{\ell,b_0}(b;x)=0$ for $z=x(t_b,b)$"; line 10 "$t_b=b-1$" → $z=-\hat H_0/(\hat H_1-\hat H_0)$ from the values at $x(t_b,b)=0,1$; the test $b-1\le t_b$; reason: $\hat H$ is affine in $x(t_b,b)$, so this is its root; the threshold never exceeds $b-1$, so the tests agree and the recursion terminates
--   - reading: "The first condition is equivalent to the terminal threshold of the canonical execution being zero or one." → a second conjunct: $\omega^\star\in\mathcal S_{(0,\mathbf r)}\cup\mathcal S_{\mathbf r}$ iff the terminal threshold returned by the run is $0$ or $1$, under the theorem's hypotheses; reason: the sentence is part of the theorem; it is read as a standalone equivalence (the stronger reading), with the threshold in local coordinates, which coincide with global ones for $\omega_0$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Theorem 5.17, p.25

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_IsAdmissible
import Definitions.Def_SecondBestBT_Supplement_baseState
import Definitions.Def_SecondBestBT_Supplement_alg2
import Definitions.Def_SecondBestBT_Supplement_suffixClass
import Definitions.Def_SecondBestBT_Supplement_Undominated

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- **Theorem 5.17** (characterization of undominated states; Liu–Qin–Ren–Wang, *Second-Best
Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…,
Theorem 5.17, p.25). Fix `α > 0`, `β = 1/2`, and an admissible global ratio vector
`(0, r_1, …, r_k)` with `k ≥ 1` and `r_i < ∞` for `1 ≤ i ≤ k`. Write `r = (r_1, …, r_k)` and let
`ω⋆ := ALG2(ω0; r)`. Then `ω⋆` is undominated iff
* `ω⋆ ∈ S_{(0,r)} ∪ S_r`, and
* `ALG2(ω0; r') ∈ S_{(0,r')}` for every nonempty proper suffix `r'` of `r`.

The first condition is equivalent to the terminal threshold of the canonical execution being zero
or one.

**Formalization Note** `ALG2` is Algorithm 2 with the normalized residual of Eq. (13)
(`alg2`, `alg2Run`), `ω0 = (β/(1 + α) ; 0)` (`baseState`), achievable states and suffix classes
are those of Definition 5.1 (through Algorithm 1, the published `greedyRun`), and dominance is
Definition 5.2; `β = 1/2` throughout. `ALG2` returns an `Option`; "`ω⋆` is undominated" and
"`ω⋆ ∈ S`" are read as: the run does not fail and its output state has the property. The
trailing sentence is the second conjunct; the terminal threshold is the one returned by
`alg2Run` (local coordinates, so `0` is the global threshold `0`). -/
theorem theorem_5_17 (α : ℝ) (hα : 0 < α) (r : List ℝ≥0∞) (hk : 1 ≤ r.length)
    (hfin : ∀ v ∈ r, v ≠ ⊤) (hadm : IsAdmissible α (0 :: r)) :
    ((∃ ω, alg2 α (1 / 2) (baseState α (1 / 2)) r = some ω ∧ Undominated α (1 / 2) ω) ↔
      ((∃ ω, alg2 α (1 / 2) (baseState α (1 / 2)) r = some ω ∧
          (ω ∈ suffixClass α (1 / 2) (0 :: r) ∨ ω ∈ suffixClass α (1 / 2) r)) ∧
        ∀ r' : List ℝ≥0∞, r' ≠ [] → r' <:+ r → r' ≠ r →
          ∃ ω', alg2 α (1 / 2) (baseState α (1 / 2)) r' = some ω' ∧
            ω' ∈ suffixClass α (1 / 2) (0 :: r'))) ∧
    ((∃ ω, alg2 α (1 / 2) (baseState α (1 / 2)) r = some ω ∧
        (ω ∈ suffixClass α (1 / 2) (0 :: r) ∨ ω ∈ suffixClass α (1 / 2) r)) ↔
      ∃ x t, alg2Run α (1 / 2) (baseState α (1 / 2)) r = some (x, t) ∧ (t = 0 ∨ t = 1)) := by sorry

end SecondBestBT.Supplement
