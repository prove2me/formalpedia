-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_clauseTerm_abs_le
-- name    : QAOAE3Lin2.Typical.clauseTerm_abs_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-16T12:53:56.108033+00:00
-- url     : https://prove2.me/theorems/dac30658-9dcb-4467-991d-17a694cf6e4c
-- title:
--   p. 11 — each clause term $\tfrac12 d_{abc}\langle Z_aZ_bZ_c\rangle$ of (55) is at most $\tfrac12$ in absolute value
-- statement:
--   Consider an E3LIN2 instance on $n$ bits with $m$ equations: equation $i$ is $x_a + x_b + x_c \equiv \mathrm{rhs}_i \pmod 2$ on the triple $(a,b,c)$ of bits, and $d_{abc} = (-1)^{\mathrm{rhs}_i} \in \{+1,-1\}$ is its sign. Let $|{-\gamma},\pi/4\rangle$ be the level-one QAOA state for this instance at phase angle $-\gamma$ and mixer angle $\pi/4$, and let
--
--   $$T_i(\gamma) \;=\; \tfrac12\, d_{abc}\, \langle -\gamma,\pi/4|\, Z_a Z_b Z_c \,|{-\gamma},\pi/4\rangle$$
--
--   be the clause term of equation $i$, the summand of (55). Then for every instance, every equation $i$ and every real $\gamma$,
--
--   $$|T_i(\gamma)| \;\le\; \tfrac12 .$$
--
--   The reason is that $Z_a Z_b Z_c$ has eigenvalues $\pm1$ and the QAOA state is a unit vector, so the expectation lies in $[-1,1]$. This bound is what turns the count of correlated pairs of equations on p. 11 into the variance bound $\tfrac14 m(6D+3)(D+1)$: each covariance of two clause terms is at most $\tfrac14$.
--
--   **Formalization Note** The expectation is written as the sum over basis strings $x$ of the measurement probability of $x$ times the product of the three spins $(-1)^{x_a}(-1)^{x_b}(-1)^{x_c}$, which is exact because the $Z$'s are diagonal. No hypothesis on the triples is needed.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, the paragraph after (57) (the bound on each term of (55) used for the variance), with (55)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- p. 11 (the variance paragraph after (57)): the clause term of equation `i`,
`½ d_abc ⟨−γ, π/4| Z_a Z_b Z_c |−γ, π/4⟩`, has absolute value at most `½`, because `d_abc = ±1`
and the expectation of the `±1`-valued observable `Z_a Z_b Z_c` in a unit vector lies in
`[−1, 1]`. -/
theorem clauseTerm_abs_le {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (γ : ℝ) :
    |clauseTerm tri rhs i γ| ≤ 1 / 2 := by sorry

end QAOAE3Lin2.Typical
