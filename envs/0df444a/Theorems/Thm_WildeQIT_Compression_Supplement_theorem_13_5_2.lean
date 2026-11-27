-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_13_5_2
-- name    : WildeQIT.Compression.Supplement.theorem_13_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:15:16.316966+00:00
-- url     : https://prove2.me/theorems/2113fcad-6163-550b-a443-5dee09534fe8
-- title:
--   Theorem 13.5.2: the coherent information $I_c(\rho,\mathcal N)$ of a degradable channel is concave in $\rho$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a degradable quantum channel with complementary channel $\mathcal N^c_{A'\to E}$, and write
--
--   $$
--   I_c(\rho,\mathcal N)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))
--   $$
--
--   for the coherent information of the channel at the input $\rho$. Then $I_c(\cdot,\mathcal N)$ is concave: for every finite ensemble $\{p_X(x),\rho_x\}$ of density operators,
--
--   $$
--   \sum_xp_X(x)\,I_c(\rho_x,\mathcal N)\le I_c\Big(\sum_xp_X(x)\rho_x,\mathcal N\Big).
--   $$
--
--   Concavity makes the optimization defining the coherent information of a degradable channel a convex problem.
--
--   **Formalization Note** Degradability is the published `WildeQIT.Degradable.IsDegradable`; $\mathcal N^c$ is the published complementary channel of the canonical isometric extension (another complementary channel differs by an isometry and gives the same entropies); $H$ is the von Neumann entropy in bits; the alphabet is any finite type.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.5.2, p. 415, eq. (13.170); Exercise 13.5.1, eq. (13.148), p. 411

import Mathlib
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Definitions.Def_WildeQIT_Degradable_complementaryApply
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.5.2, p. 415.
-/

namespace WildeQIT.Compression.Supplement

open Classical in
/-- **Theorem 13.5.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 415, (13.170)): "Suppose that a quantum channel `N` is
degradable. Then the coherent information `I_c(ρ, N)` is concave in the input density operator:
`∑_x p_X(x) I_c(ρ_x, N) ≤ I_c(∑_x p_X(x) ρ_x, N)`, where `p_X(x)` is a probability density function
and each `ρ_x` is a density operator", with `I_c(ρ, N) ≡ H(N(ρ)) − H(N^c(ρ))` (13.148).

Formalization Note: the ensemble has any finite alphabet `X` with the published `FinDist`
distribution ("probability density function" of a discrete variable). Degradability is the
published `WildeQIT.Degradable.IsDegradable`; `N^c` is the published complementary channel of the
canonical isometric extension (any other complementary channel gives the same entropy); `H` is
the published `QAlgorithms.vnEntropy` (bits). Decidable equality on the environment is
classical. -/
theorem theorem_13_5_2 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QChannel a b) (hN : WildeQIT.Degradable.IsDegradable N) {X : Type} [Fintype X]
    (p : FinDist X) (ρ : X → Matrix a a ℂ) (hρ : ∀ x, IsDensityOperator (ρ x)) :
    ∑ x, p.prob x * (QAlgorithms.vnEntropy (N.apply (ρ x)) -
        QAlgorithms.vnEntropy (WildeQIT.Degradable.complementaryApply N (ρ x))) ≤
      QAlgorithms.vnEntropy (N.apply (∑ x, ((p.prob x : ℝ) : ℂ) • ρ x)) -
        QAlgorithms.vnEntropy
          (WildeQIT.Degradable.complementaryApply N (∑ x, ((p.prob x : ℝ) : ℂ) • ρ x)) := by sorry

end WildeQIT.Compression.Supplement
