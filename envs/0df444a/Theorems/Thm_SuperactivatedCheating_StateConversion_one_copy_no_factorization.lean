-- Prove2me | Theorems.Thm_SuperactivatedCheating_StateConversion_one_copy_no_factorization
-- name    : SuperactivatedCheating.StateConversion.one_copy_no_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:13.646594+00:00
-- url     : https://prove2.me/theorems/e5d82ce2-f550-4ba6-8128-874221fef6de
-- title:
--   Proof of Theorem 11, p. 16 — one copy of p does not factor through q
-- statement:
--   A probability vector is a finitely indexed nonnegative real vector summing to 1. $(u\otimes v)_{(i,j)}=u_iv_j$ and $p^{\otimes n}_x=\prod_i p_{x_i}$ for strings $x$ of length $n$. "$u=v$ up to a permutation" for vectors of possibly different lengths means that their multisets of nonzero entries coincide. For probability vectors $p\in\mathbb R^k$, $q\in\mathbb R^l$, the state-conversion game $G_{SC}(p,q)$ has trivial referee register, question state $|\psi_p\rangle=\sum_i\sqrt{p_i}\,|i,i\rangle$ and accepting projection $|\phi_q\rangle\langle\phi_q|$ with $|\phi_q\rangle=\sum_j\sqrt{q_j}\,|j,j\rangle$. The witnesses are $q=(1/3,2/3)$ and $p=\frac1{201}(1,2,2,4,4,4,8,16,32,32,32,64)$, and the polynomials are $S(x)=1+x+2x^2-x^3+2x^4+x^5$ and $P(x)=(1+x)S(x)$ over $\mathbb Z$.
--
--   For the witnesses $p$, $q$ and every probability vector $s$ of every finite length $d$, $p\ne q\otimes s$ up to a permutation.
--
--   Differences from the source:
--   - reading: p = q ⊗ r up to a permutation → the multisets of nonzero entries of p and of q ⊗ r coincide; reason: the vectors have different lengths and zero entries carry no Schmidt coefficient; a literal bijection of full index sets would make the criterion false (p = (1/2, 1/2, 0) converts to q = (1/2, 1/2) by local relabelling, yet 3 is not a multiple of 2)
--   - encoding: 1-based indices i, j → 0-based Fin k, Fin l; reason: relabelling only
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, proof of Theorem 11, p. 16

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_GameSC

namespace SuperactivatedCheating.StateConversion

/-- Proof of Theorem 11, p. 16: for the witness `p`, `q`, `p ≠ q ⊗ s` up to a permutation for
every probability vector `s` of every finite length. -/
theorem one_copy_no_factorization (d : ℕ) (s : Fin d → ℝ) (hs : IsProbVec s) :
    ¬ EqUpToPerm pWit (vtensor qWit s) := by sorry

end SuperactivatedCheating.StateConversion
