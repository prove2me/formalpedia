-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_4_1
-- name    : ParityBarrier563.Trilinear.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:12.646313+00:00
-- url     : https://prove2.me/theorems/2c2006f6-9fe6-4dfe-b76c-584af60a8bee
-- title:
--   Lemma 4.1 — a satisfiable b-CNF whose short terms are well spread is cl_b of O(b log(2|V|+2)/τ) satisfying assignments
-- statement:
--   Let $V$ be a finite set of variables, $b\ge1$ an integer and $0<\tau\le1$. Let $H$ be a satisfiable $b$-CNF on $\{0,1\}^V$ such that every term $\pi$ of width at most $b$ satisfies
--
--   $$\mathbb E[H\pi]=0\quad\text{or}\quad \mathbb E[H\pi]\ge\tau\,\mathbb E[H].$$
--
--   Then $H=\mathrm{cl}_b(S)$ for some set $S$ of satisfying assignments of $H$ with
--
--   $$|S|\le K\cdot\frac{b\log_2(2|V|+2)}{\tau},$$
--
--   where $K>0$ is an absolute constant (the same for all $V,b,\tau,H$).
--
--   This is the base case of the decomposition theorem: a $b$-CNF in which no short term carves out a small nonzero fraction of its satisfying assignments is determined by a few of them.
--
--   Differences from the source:
--   - encoding: S of at most O(b log(2|V|+2)/τ) satisfying assignments → ∃ K > 0, chosen before V, b, τ and H, with |S| ≤ K·b·log₂(2|V|+2)/τ; reason: the O-constant of the source is absolute; logarithms are base two (§2)
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 4.1, printed p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 4.1, printed p.14 / PDF 16. -/
theorem lemma_4_1 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (b : ℕ) (τ : ℝ) (H : BoolFn V),
        1 ≤ b → 0 < τ → τ ≤ 1 → IsCNF b H → (∃ x, H x = true) →
        (∀ π : LitSet V, width π ≤ b →
          avg (fun x => ind H x * ind (termFn π) x) = 0 ∨
            τ * avg (ind H) ≤ avg (fun x => ind H x * ind (termFn π) x)) →
        ∃ S : Finset (V → Bool), (∀ x ∈ S, H x = true) ∧
          (S.card : ℝ) ≤ K * ((b : ℝ) * Real.logb 2 (2 * Fintype.card V + 2) / τ) ∧
          closure b S = H := by sorry

end ParityBarrier563.Trilinear
