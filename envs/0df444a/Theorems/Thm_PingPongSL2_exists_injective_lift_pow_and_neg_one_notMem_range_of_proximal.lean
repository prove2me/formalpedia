-- Prove2me | Theorems.Thm_PingPongSL2_exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal
-- name    : PingPongSL2.exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:57:22.947022+00:00
-- url     : https://prove2.me/theorems/f157eca3-a351-4520-b336-d696c9aea6bf
-- title:
--   Ping-pong in SL₂ over a normed field — powers of a proximal element and a conjugate are free
-- statement:
--   Let $L$ be a normed field with $2 \ne 0$, and let $x, c \in \mathrm{SL}_2(L)$. Suppose $x$ has trace $\mu + \mu^{-1}$ for some $\mu \in L$ with $\|\mu\| > 1$, and the commutator $[x, cxc^{-1}] = x \cdot cxc^{-1} \cdot x^{-1} \cdot (cxc^{-1})^{-1}$ has trace different from $2$. Then for some $N \ge 1$ the elements $x^N$ and $c x^N c^{-1}$ freely generate a free group of rank two that does not contain $-1$.
--
--   Precisely: the homomorphism from the free group on two generators to $\mathrm{SL}_2(L)$ sending them to $x^N$ and $c x^N c^{-1}$ is injective, and $-1$ is not in its image. The trace condition on the commutator says that $x$ and $cxc^{-1}$ have no common eigenvector, so their attracting and repelling points on the projective line are four distinct points.
--
--   Tits states (p. 263, Proposition 3.12): "Let $Y$ be a finite set of semisimple elements of $PGL(P)$. Suppose that for all $x \in Y$, $A(x)$ and $A(x^{-1})$ are one-point sets and that, for $x, y \in Y$ with $x \ne y$, one has $A(x) \cup A(x^{-1}) \subset P - A'(y) - A'(y^{-1})$. Then, there exists $M \in \mathbf N$ such that, for all $m \in \mathbf N$ greater than $M$, the set $Y^m = \{x^m \mid x \in Y\}$ is free in $PGL(P)$." Here $A$ and $A'$ are the attracting and repulsing subspaces (§3.6, p. 258), and the field is locally compact (§3.1, p. 256). The statement here is the case $Y = \{x, cxc^{-1}\}$ on the projective line, over any normed field, with the transversality given by the trace condition; it concludes for one power $N$, and it lifts the freeness from $\mathrm{PGL}_2$ to $\mathrm{SL}_2$ by excluding $-1$ from the image. Together with `TitsLemma.exists_ringHom_proximal` it gives free subgroups of $\mathrm{SL}_2(\mathbb R)$ containing a power of a given element.
-- source:
--   Tits, J., Free subgroups in linear groups, J. Algebra 20 (1972) 250–270, https://doi.org/10.1016/0021-8693(72)90058-0, p. 263, Proposition 3.12, for Y = {x, cxc⁻¹} in SL(2) over a normed field (with Proposition 1.1, p. 253, the ping-pong criterion it rests on)

import Mathlib

namespace PingPongSL2

theorem exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal {L : Type} [NormedField L] (h2 : (2 : L) ≠ 0)
    (x c : Matrix.SpecialLinearGroup (Fin 2) L) (μ : L) (hμ : 1 < ‖μ‖)
    (hx : μ + μ⁻¹ = (x : Matrix (Fin 2) (Fin 2) L).trace)
    (hc : ((x * (c * x * c⁻¹) * x⁻¹ * (c * x * c⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace ≠ 2) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]) ∧
      (-1 : Matrix.SpecialLinearGroup (Fin 2) L) ∉ (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]).range := by
  sorry

end PingPongSL2
