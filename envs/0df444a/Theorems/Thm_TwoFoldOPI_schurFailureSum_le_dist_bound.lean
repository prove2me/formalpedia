-- Prove2me | Theorems.Thm_TwoFoldOPI_schurFailureSum_le_dist_bound
-- name    : TwoFoldOPI.schurFailureSum_le_dist_bound
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-10T18:54:35.841858+00:00
-- url     : https://prove2.me/theorems/48461fb2-fa2a-415a-b932-1276d1cd8e5d
-- title:
--   Lemma 7.3, second bound — $E(D)\le q^{\dim D+\dim D^{*2}}/(q-1)^{\mathrm{dist}(D)}$
-- statement:
--   Let $K=\mathbb F_q$ be a finite field, $M\ge 0$, and let $D\subseteq\mathbb F_q^M$ be any linear code (in the mission $D=C^\perp$). For $c\in\mathbb F_q^M$ write $\mathrm{wt}(c)$ for its Hamming weight and $Z(c)=\{i : c_i=0\}$ for its zero set; for a code $W$ and $S\subseteq[M]$ let $W[S]=\{w\in W : w_i=0\ \forall i\in S\}$ be the shortened code, and let $D^{*2}$ be the Schur square of $D$ (the span of all coordinate-wise products $u\odot v$, $u,v\in D$). Let $\mathrm{dist}(D)$ be the least weight of a nonzero word of $D$. Then the ambiguity sum of Lemma 7.3 satisfies
--
--   $$
--   E(D)=\sum_{c\in D\setminus\{0\}}\frac{q^{\dim (D^{*2})[Z(c)]}}{(q-1)^{\mathrm{wt}(c)}}\ \le\ \frac{q^{\dim D+\dim D^{*2}}}{(q-1)^{\mathrm{dist}(D)}} .
--   $$
--
--   This is the second inequality of Lemma 7.3 (equivalently, after multiplying by $2|D|=2q^{\dim D}$, the second inequality of Theorem 7.4): it replaces the refined failure sum, which depends on the shortened Schur squares, by a bound that only involves the distance of $D$ and the dimensions of $D$ and of its Schur square.
--
--   **Formalization Note.** $q=|K|$, $\dim$ is `Module.finrank K`, and $\mathrm{dist}(D)$ is `minDist D`, which equals $0$ for $D=\{0\}$ by the convention `sInf ∅ = 0`. The inequality is stated for every linear code; for $D=\{0\}$ the left side is the empty sum $0$ and the right side is $q^{\dim D^{*2}}\ge 0$, so no hypothesis $D\neq\{0\}$ is needed. The case $q=2$ is allowed.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held), §7.2, Lemma 7.3, p.39 (displayed second inequality) and its proof, p.40: "Bounding each of the fewer than q^{dim C⊥} terms by q^{dim((C⊥)^{∗2})}(q−1)^{−dist(C⊥)} gives the second bound"; also the second inequality of Theorem 7.4, p.40.

import Mathlib
import Definitions.Def_TwoFoldOPI_schurFailureSum
import Definitions.Def_TwoFoldOPI_minDist

namespace TwoFoldOPI

theorem schurFailureSum_le_dist_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K] {M : ℕ}
    (D : Submodule K (Fin M → K)) :
    schurFailureSum D ≤
      (Fintype.card K : ℝ) ^ (Module.finrank K D + Module.finrank K (schurSquare D)) /
        ((Fintype.card K : ℝ) - 1) ^ minDist D := by sorry

end TwoFoldOPI
