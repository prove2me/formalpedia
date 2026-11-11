-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5_law
-- name    : SampleMLS.ExpMoment.theorem_3_5_law
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:41.820248+00:00
-- url     : https://prove2.me/theorems/bb12ce4c-0915-4792-ac46-33f6b52a9bfb
-- title:
--   Theorem 3.5(ii)–(iii) for the law of Algorithm 3.4 — probability 0 of yes when F has no set of size ≤ k, at least 1 − e^{−κ} under (⋆)
-- statement:
--   Fix an instance: a finite universe $U$ with $n=|U|$, a family $F$ of subsets of $U$, a size bound $k\le n$, and $g(X)\ge0$ for $X\subseteq U$, $|X|\le k$. Let $\psi\ge0$, $\Gamma\ge1$, $\kappa>0$, and let $\Theta$ and $m_{t,\theta}$ satisfy (2). Run Algorithm 3.4 with a correct extension algorithm, i.e. a trial accepts $X$ iff $g(X)\le\theta$ and $X$ lies in a set of $F$ with at most $k$ elements. Then (ii) if $F$ has no set of size at most $k$, the algorithm answers yes with probability $0$; (iii) if some $S\in F$ with $|S|=k$ satisfies (⋆), it answers yes with probability at least $1-e^{-\kappa}$.
--
--   Differences from the source:
--   - encoding: Algorithm 3.4 run with a deterministic correct extension algorithm A → mlsLaw U gk (fun X => extYes U F X k) k Θ m, the law of the trial loop with the extension answers in place of A; reason: A is deterministic and solves Φ-Extension, so it accepts (I, X, k) exactly when extYes holds; the time of A plays no role in (ii)–(iii)
--   - encoding: (ii) "answers no" → the law gives probability 0 to yes; reason: for the law of the answer this is the same statement; the every-outcome form is in the goal theorem
--   - encoding: integer trial counts; probabilities → m : ℕ → ℤ → ℕ; probabilities in ℝ≥0∞, the bound as ENNReal.ofReal (1 − e^{−κ}); reason: (2) forces m_{t,θ} > 0; 1 − e^{−κ} > 0
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), Theorem 3.5(ii)–(iii), p. 17 (PDF 19), with Algorithm 3.4, p. 16 (PDF 18), and the proof, pp. 18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Theorem 3.5(ii)–(iii) for the law of Algorithm 3.4, pp. 16–19 (PDF 18–21): with a cap and
trial counts satisfying (2) and a correct extension algorithm, MLS-θ answers yes with probability
`0` if `F` has no set of size at most `k`, and with probability at least `1 − e^{−κ}` if some
`S ∈ F` with `|S| = k` satisfies (⋆). -/
theorem theorem_3_5_law (U : Finset ℕ) (F : Set (Finset ℕ)) (hF : ∀ S ∈ F, S ⊆ U)
    (gk : Finset ℕ → ℝ) (k : ℕ) (hk : k ≤ U.card) (hg : ∀ X ⊆ U, X.card ≤ k → 0 ≤ gk X)
    (ψ Γ κ : ℝ) (hψ : 0 ≤ ψ) (hΓ : 1 ≤ Γ) (hκ : 0 < κ) (Θ : ℤ) (m : ℕ → ℤ → ℕ)
    (h2 : Cond2 ψ Γ κ U.card k Θ m) :
    ((¬ ∃ S ∈ F, S.card ≤ k) → mlsLaw U gk (fun X => extYes U F X k) k Θ m true = 0) ∧
    (∀ S ∈ F, S.card = k → Star gk U S ψ Γ →
      ENNReal.ofReal (1 - Real.exp (-κ)) ≤ mlsLaw U gk (fun X => extYes U F X k) k Θ m true) := by sorry

end SampleMLS.ExpMoment
