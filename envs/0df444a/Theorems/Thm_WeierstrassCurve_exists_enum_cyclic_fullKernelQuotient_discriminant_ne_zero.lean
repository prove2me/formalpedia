-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
-- name    : WeierstrassCurve.exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/88665ac3-dc50-5853-94e6-8be4708cbf76
-- title:
--   Enumerating the ψ(N) cyclic N-subgroups with nonsingular Vélu quotients
-- statement:
--   Let $K$ be an algebraically closed field equipped with decidable equality, let $N$ be a natural number with $N \neq 0$ and assume moreover that the image of $N$ in $K$ is nonzero, and let $W$ be a Weierstrass curve over $K$ which is elliptic. The assertion is that there exist an index type $\iota$ carrying a `Fintype` structure whose cardinality equals $\mathrm{dedekindPsi}\,N = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, together with a family $Q : \iota \to W(K)$ of points of the affine model of $W$, such that: each $Q_i$ has additive order exactly $N$; the map sending $i$ to the subgroup `AddSubgroup.zmultiples (Q i)` of integer multiples of $Q_i$ is injective, so the cyclic subgroups $\langle Q_i \rangle$ are pairwise distinct; and for every $i$ the discriminant of the curve `W.fullKernelQuotient (Q i) N` is nonzero. Here that curve is the Weierstrass curve with the same $a_1, a_2, a_3$ as $W$, with $a_4$ replaced by $a_4 - 5t$ and $a_6$ by $a_6 - b_2 t - 7w$, where $t$ and $w$ are Vélu's sums $\sum (3x^2 + 2a_2 x + a_4 - a_1 y)$ and $\sum (x(3x^2 + 2a_2 x + a_4 - a_1 y) + y(2y + a_1 x + a_3))$ taken over the set of coordinate pairs of the multiples $Q_i, 2Q_i, \dots, (N-1)Q_i$.
--
--   This is the statement that over an algebraically closed field in which $N$ is invertible an elliptic curve has exactly $\psi(N)$ cyclic subgroups of order $N$, each presented by a generator, and that Vélu's explicit quotient equations for each such subgroup again define a nonsingular curve. It is used in the construction of the modular function field of level $N$, where the $j$-invariants of these quotients are matched with the values of $j(q^N)$-type functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem WeierstrassCurve.exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = dedekindPsi N ∧
      ∃ Q : ι → W.toAffine.Point, (∀ i, addOrderOf (Q i) = N) ∧
        Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧
        ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0 := by sorry
