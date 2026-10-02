-- Prove2me | Theorems.Thm_TeschlQM_Atomic_exists_localization_partition
-- name    : TeschlQM.Atomic.exists_localization_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:07:58.807005+00:00
-- url     : https://prove2.me/theorems/b43a7360-0366-4a4d-a8f9-da1403f7fa0a
-- title:
--   Lemma 11.4 — a partition of unity separating the electrons from the nucleus
-- statement:
--   Let $n = 3N$ and write $x = (x_1, \dots, x_N) \in \mathbb R^{3N}$ with $x_j \in \mathbb R^3$. Fix some $C \in (0, 1/\sqrt N)$. There exist smooth functions $\varphi_j \in C^\infty(\mathbb R^n, [0,1])$, $1 \le j \le N$, such that $\sum_{j=1}^N \varphi_j(x)^2 = 1$ for all $x$,
--   $$\operatorname{supp}(\varphi_j) \cap \{x \mid |x| \ge 1\} \subseteq \{x \mid |x_j| \ge C|x|\},$$
--   and $|\partial\varphi_j(x)| \to 0$ as $|x| \to \infty$.
--
--   Combined with the IMS formula, this partition exhibits the atomic Hamiltonian, outside a ball, as a sum of pieces in each of which one electron is far from the nucleus.
--
--   **Formalization Note.** $\mathbb R^{3N}$ is `EuclideanSpace ℝ (Fin N × Fin 3)` and $x_j$ is `electron x j`; $\operatorname{supp}$ is the closed support `tsupport`; $|\partial\varphi_j(x)|$ is `‖fderiv ℝ (φ j) x‖`, and $|x| \to \infty$ is the cocompact filter. For $N = 0$ the interval $(0, 1/\sqrt N)$ is empty in Lean ($1/\sqrt 0 = 0$), so the statement is vacuous there, as in the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 243, Lemma 11.4

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

namespace TeschlQM.Atomic

open Filter Topology
open scoped ContDiff

/-- Teschl, Lemma 11.4, p. 243. Fix some `C ∈ (0, 1/√N)`. There exist smooth functions
`φ_j ∈ C^∞(ℝⁿ, [0, 1])`, `1 ≤ j ≤ N`, `n = 3N`, such that `∑_j φ_j(x)² = 1` (11.12),
`supp(φ_j) ∩ {x | |x| ≥ 1} ⊆ {x | |x_j| ≥ C|x|}` (11.14), and `|∂φ_j(x)| → 0` as `|x| → ∞`.
Here `x_j ∈ ℝ³` is the `j`-th electron's position (`electron x j`), `supp` is the closed support
`tsupport`, and `|∂φ_j(x)|` is the norm of the derivative. -/
theorem exists_localization_partition (N : ℕ) (C : ℝ) (hC0 : 0 < C)
    (hC : C < 1 / Real.sqrt N) :
    ∃ φ : Fin N → EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j x, φ j x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, ∑ j, φ j x ^ 2 = 1) ∧
      (∀ j, tsupport (φ j) ∩ {x | 1 ≤ ‖x‖} ⊆ {x | C * ‖x‖ ≤ ‖electron x j‖}) ∧
      (∀ j, Tendsto (fun x => ‖fderiv ℝ (φ j) x‖) (cocompact _) (𝓝 0)) := by sorry

end TeschlQM.Atomic
