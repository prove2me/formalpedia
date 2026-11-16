-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_6_9
-- name    : QVolTransducer.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:41:42.52421+00:00
-- url     : https://prove2.me/theorems/e9486310-cd0b-4e6c-8b05-4f1d439101cc
-- title:
--   Theorem 6.9 — multiplicative perturbations: $\|P_x-P'_x\|_{\mathrm{TV}}\le\eta$ and $|\pi'_x/\pi_x-1|<3D\eta$
-- statement:
--   Let $(\Omega,P)$ and $(\Omega,P')$ be reversible, irreducible random walks on a finite state space with stationary distributions $\pi,\pi'$, such that $P_{xy}\ne0\Leftrightarrow P'_{xy}\ne0$ for all $x,y$, and let $D$ be the diameter of the underlying graph. Let $0<\eta<1/(32D)$ and suppose that
--
--   $$\Big|\frac{P'_{xy}}{P_{xy}}-1\Big|\le\eta\qquad\text{whenever }P_{xy}\ne0\text{ and }x\ne y.$$
--
--   Then for every $x\in\Omega$,
--
--   $$\|P_{x\cdot}-P'_{x\cdot}\|_{\mathrm{TV}}\le\eta\qquad\text{and}\qquad\Big|\frac{\pi'_x}{\pi_x}-1\Big|<3D\eta.$$
--
--   A small relative perturbation of the transition probabilities thus perturbs the stationary distribution by at most a factor $1\pm3D\eta$.
--
--   **Formalization Note** The underlying graph has an edge $x\sim y$ ($x\ne y$) iff $P_{xy}\ne0$, and $D$ is its graph diameter. The bound is written literally $\eta<1/(32D)$; for a one-state chain ($D=0$) it excludes every $\eta$, as the undefined printed bound does. $\|\cdot\|_{\mathrm{TV}}=\tfrac12\sum_y|\cdot|$.
--
--   Differences from the source:
--   - encoding: reversible, irreducible random walks with stationary distributions π, π′ → stochastic matrices, MarkovMixing.Irreducible, IsDist and DetailedBalance (published mm_basic); reason: detailed balance with a distribution is reversibility, and it makes the distribution stationary
--   - encoding: D, the diameter of the underlying graph → SimpleGraph.diam of SimpleGraph.fromRel (P x y ≠ 0); reason: edges between distinct states with positive transition probability; symmetric by reversibility
--   - encoding: 0 < η < 1/(32D), undefined when D = 0 (a one-state chain) → η < 1/(32·D) with Lean's 1/0 = 0, so no η qualifies when D = 0; reason: excludes only the case where the printed bound is undefined (there the printed strict conclusion |π′_x/π_x − 1| < 0 could not hold)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 6.9, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_mm_basic

namespace QVolTransducer.Supplement

/-- **Multiplicative perturbations of a finite reversible chain** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 6.9, p.41 (PDF p.43)).

Let `(Ω, P)` and `(Ω, P′)` be reversible, irreducible random walks on a finite state space with
stationary distributions `π, π′`, with `P_{xy} ≠ 0 ⇔ P′_{xy} ≠ 0` for all `x, y`, and let `D` be the
diameter of the underlying graph. Let `0 < η < 1/(32D)` and suppose `|P′_{xy}/P_{xy} − 1| ≤ η`
whenever `P_{xy} ≠ 0` and `x ≠ y`. Then for all `x ∈ Ω`, `‖P_{x·} − P′_{x·}‖_TV ≤ η` and
`|π′_x/π_x − 1| < 3Dη`.

**Formalization Note** The chains are stochastic matrices (`MarkovMixing.IsStochastic`), irreducible
and in detailed balance with the distributions `π`, `π′` (published `mm_basic`). The underlying
graph has an edge `x ~ y` (`x ≠ y`) iff `P_{xy} ≠ 0` (`SimpleGraph.fromRel`, which symmetrizes; by
reversibility the relation is already symmetric), and `D` is its `SimpleGraph.diam`. The hypothesis
is written literally `η < 1/(32 D)`: for `D = 0` (one state) Lean's `1/0 = 0` excludes every `η`,
as the paper's undefined bound does. `‖·‖_TV = ½ Σ_y |·|`. -/
theorem theorem_6_9 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P P' : Matrix Ω Ω ℝ) (π π' : Ω → ℝ)
    (hP : MarkovMixing.IsStochastic P) (hP' : MarkovMixing.IsStochastic P')
    (hirr : MarkovMixing.Irreducible P) (hirr' : MarkovMixing.Irreducible P')
    (hπ : MarkovMixing.IsDist π) (hπ' : MarkovMixing.IsDist π')
    (hrev : MarkovMixing.DetailedBalance P π) (hrev' : MarkovMixing.DetailedBalance P' π')
    (hsupp : ∀ x y, P x y ≠ 0 ↔ P' x y ≠ 0) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < 1 / (32 * ((SimpleGraph.fromRel fun x y => P x y ≠ 0).diam : ℝ)))
    (hratio : ∀ x y, P x y ≠ 0 → x ≠ y → |P' x y / P x y - 1| ≤ η) :
    ∀ x, (1 / 2) * ∑ y, |P x y - P' x y| ≤ η ∧
      |π' x / π x - 1| < 3 * ((SimpleGraph.fromRel fun x y => P x y ≠ 0).diam : ℝ) * η := by sorry

end QVolTransducer.Supplement
