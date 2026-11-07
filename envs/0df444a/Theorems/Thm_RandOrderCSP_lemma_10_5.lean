-- Prove2me | Theorems.Thm_RandOrderCSP_lemma_10_5
-- name    : RandOrderCSP.lemma_10_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:59.906847+00:00
-- url     : https://prove2.me/theorems/c6f4c575-45aa-4221-808f-a709b24b91a0
-- title:
--   Lemma 10.5 — distinguishing CSP values from regularized neighborhoods
-- statement:
--   For every $k\ge2$, finite alphabet $\Sigma$ and $\varepsilon\in(0,1)$ there are integers $D,R\ge1$ and a deterministic $v:\mathcal N_{D,R,\{0,1\}^{\Sigma^k}}\to[0,1]$ such that for every predicate family $\Gamma$ and thresholds $0\le\beta<\gamma\le1$ with $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ roundable, every instance $\Phi$ of $\mathrm{CSP}(\Gamma)$ satisfies
--
--   $$\mathrm{opt}_\Phi\ge\gamma+\varepsilon\Rightarrow\mathbb E_{N\sim\text{Red-Nbhd-Type}_{D,R}(\Phi)}[v(N)]\ge\gamma+\tfrac34\varepsilon,$$
--
--   $$\mathrm{opt}_\Phi\le\beta-\varepsilon\Rightarrow\mathbb E_{N\sim\text{Red-Nbhd-Type}_{D,R}(\Phi)}[v(N)]\le\gamma+\tfrac14\varepsilon.$$
--
--   The upper bound therefore reduces to estimating the reduced neighbourhood type distribution.
--
--   Differences from the source:
--   - encoding: v : N_{D,R,{0,1}^{Σ^k}} → [0, 1] → v on all finite rooted classes with values in [0, 1]; reason: a function on the subset extends by 0 and only types of D-regular instances are evaluated
--   - encoding: finite alphabet Σ and every instance Φ → [Nonempty Sig] and a nonempty edge set; reason: the standing assumptions of §3.3 and §10
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Lemma 10.5, p.51

import Mathlib
import Definitions.Def_RandOrderCSP_HasIntegralityGap
import Definitions.Def_RandOrderCSP_regularize

namespace RandOrderCSP

/-- **Lemma 10.5 (distinguishing CSP values from regularized neighborhoods).** Singer, Tulsiani, Velusamy,
*A dichotomy theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript
sha256 3aca9d2f…), Lemma 10.5, p.51.

**Formalization Note.** `D`, `R`, `v` are chosen before `Γ`, `β`, `γ`, as printed. Roundable is
`¬ HasIntegralityGap Γ β γ` (p.14). `v` is total on rooted classes with values in `[0,1]`: the printed `v`
on `N_{D,R,{0,1}^{Σ^k}}` extends by `0`, and only types of `D`-regular instances are evaluated. -/
theorem lemma_10_5 {k : ℕ} (hk : 2 ≤ k) (Sig : Type) [Fintype Sig] [DecidableEq Sig] [Nonempty Sig]
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ (D R : ℕ) (v : RootedClass k ((Fin k → Sig) → Bool) → ℝ), 1 ≤ D ∧ 1 ≤ R ∧
      (∀ N, 0 ≤ v N ∧ v N ≤ 1) ∧
      ∀ (Γ : Set ((Fin k → Sig) → Bool)) (β γ : ℝ), 0 ≤ β → β < γ → γ ≤ 1 →
        ¬ HasIntegralityGap Γ β γ →
        ∀ (V E : Type) [Fintype V] [Fintype E] [Nonempty E] (Φ : CSP k Sig V E), Φ.IsInstanceOf Γ →
          (γ + ε ≤ Φ.opt → γ + 3 / 4 * ε ≤ redNbhdExpect Φ.H Φ.f D R v) ∧
          (Φ.opt ≤ β - ε → redNbhdExpect Φ.H Φ.f D R v ≤ γ + 1 / 4 * ε) := by sorry

end RandOrderCSP
