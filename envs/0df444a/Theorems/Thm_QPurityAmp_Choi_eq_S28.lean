-- Prove2me | Theorems.Thm_QPurityAmp_Choi_eq_S28
-- name    : QPurityAmp.Choi.eq_S28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:24.968244+00:00
-- url     : https://prove2.me/theorems/32ed96b0-3b19-4c29-a945-e3f412ca7b9e
-- title:
--   Eqs. (S27)–(S28), p. 21 — S^[µ] ≤ S^[λ] on positive arguments iff [µ] ⪯ [λ] in dominance order
-- statement:
--   Let $\mu$ and $\lambda$ be Young diagrams with the same number $N$ of boxes and at most $d$ rows, and let $S^{[\nu]}(x)=s^{[\nu]}(x)/s^{[\nu]}(1,\dots,1)$ be the normalized Schur polynomial in $d$ variables. Then
--   $$S^{[\mu]}(x)\le S^{[\lambda]}(x)\ \text{ for all } x\in(0,\infty)^d\quad\Longleftrightarrow\quad[\mu]\preceq[\lambda],$$
--   where $[\mu]\preceq[\lambda]$ means $\sum_{a=1}^k\mu_a\le\sum_{a=1}^k\lambda_a$ for every $k$ (Eq. (S27)).
--
--   The direction $\Leftarrow$ is the Cuttler–Greene–Skandera conjecture, proved by Sra (2016), which the paper cites as Ref. [27]. In the proof of Theorem II.1 it orders the coefficients $c'_i$ of the linear program.
--
--   **Formalization Note** The printed (S28) reads $S^{[\mu]}\le S^{[\lambda]}\Leftrightarrow[\mu]\preceq[\lambda]$ with the quantifier over the arguments implicit ("for positive arguments"); it is made explicit here. Partial sums are taken for every $k\in\mathbb N$, which is equivalent to $k\in\{1,\dots,n\}$ in (S27) because both diagrams have the same size and at most $d$ rows.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 21, Eqs. (S27)–(S28)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open QAlgorithms.Schur

/-- Eqs. (S27)–(S28), p. 21: for Young diagrams µ, λ with the same number N of boxes and at most
d rows, S^[µ](x) ≤ S^[λ](x) for every x with positive entries if and only if [µ] ⪯ [λ] in the
dominance order (every partial row sum of µ is at most that of λ). -/
theorem eq_S28 {d N : ℕ} (mu la : Partition d N) :
    (∀ x : Fin d → ℝ, (∀ j, 0 < x j) → normSchur mu x ≤ normSchur la x) ↔
      DomLE mu.val la.val := by sorry

end QPurityAmp.Choi
