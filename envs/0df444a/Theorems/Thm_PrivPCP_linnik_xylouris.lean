-- Prove2me | Theorems.Thm_PrivPCP_linnik_xylouris
-- name    : PrivPCP.linnik_xylouris
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T03:08:08.433668+00:00
-- url     : https://prove2.me/theorems/73c7f64c-5593-5a33-bff8-5ade811f455b
-- title:
--   Linnik's theorem (Xylouris): a prime $q\equiv1\pmod M$ with $q\le M^6$
-- statement:
--   This is Linnik's theorem on the least prime in an arithmetic progression, in the form with Xylouris's exponent.
--
--   There is an integer $M_0$ such that for every integer $M\ge M_0$ there is a prime $q$ with
--   $$q\equiv1\pmod M,\qquad q\le M^6 .$$
--
--   Linnik's theorem bounds the least prime $p(M)\equiv1\pmod M$ by $CM^L$. Xylouris proved it with $L=5$, so $p(M)\le M^6$ once $M\ge C$. In the source this gives a prime field $\mathbb F_q$ whose multiplicative group contains subgroups of all prescribed orders $s_i$ (with $\prod_is_i\mid q-1$), while keeping $q$ polynomial in the grid size.
--
--   **Formalization Note** $q\equiv1\pmod M$ is written $M\mid q-1$ in $\mathbb N$, where $q\ge2$ because $q$ is prime.
-- source:
--   T. Xylouris, Ueber die Nullstellen der Dirichletschen L-Funktionen und die kleinste Primzahl in einer arithmetischen Progression, Bonner Math. Schriften 404 (2011) (Linnik's constant L <= 5); cited as [Xyl09] in Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), proof of Lemma 5.4, p.30 (PDF p.32): 'every sufficiently large M admits a prime q = 1 (mod M) with q <= M^6'

import Mathlib

namespace PrivPCP

theorem linnik_xylouris : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∃ q : ℕ, q.Prime ∧ M ∣ q - 1 ∧ q ≤ M ^ 6 := by sorry

end PrivPCP
