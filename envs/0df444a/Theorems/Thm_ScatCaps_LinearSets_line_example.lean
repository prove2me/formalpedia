-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_line_example
-- name    : ScatCaps.LinearSets.line_example
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:07.343074+00:00
-- url     : https://prove2.me/theorems/0965da9a-52cf-466e-b0f2-b7282ebf7bbc
-- title:
--   §1, p. 2 — for r even there is a scattered 𝔽_q-linear set of rank rt/2 in PG(r − 1, q^t) ([9, Thm 2.5.5])
-- statement:
--   Let $\mathbb F_q\subseteq\mathbb F_{q^t}$ be finite fields with $t\ge1$, and let $r\ge2$ be even. There is an $\mathbb F_q$-subspace $U$ of $V=\mathbb F_{q^t}^{\,r}$ such that
--
--   $$
--   \dim_{\mathbb F_q}U=\frac{rt}{2}\qquad\text{and}\qquad L_U=\{\langle u\rangle_{\mathbb F_{q^t}}:u\in U\setminus\{0\}\}\ \text{is scattered in }\mathrm{PG}(r-1,q^t).
--   $$
--
--   The paper quotes this from [9, Theorem 2.5.5]; the case $r=2$ (a scattered linear set of rank $t$ on a projective line) is a building block of Theorem 1.2.
--
--   **Formalization Note** $\mathrm{PG}(r-1,q^t)$ is $\mathrm{PG}(V,\mathbb F_{q^t})$ with $V$ the coordinate space `Fin r → K`. Rank $rt/2$ is $|U|=q^{rt/2}$ with exact natural division since $r$ is even.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 2, §1 (citing [9, Theorem 2.5.5])

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem line_example (K : Type*) [Field K] [Fintype K]
    (Fq : Subfield K) (q t r : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ t)
    (ht : 0 < t) (hr : 2 ≤ r) (heven : Even r) :
    ∃ U : Set (Fin r → K), IsFqSubspace Fq U ∧
      HasRank Fq U (r * t / 2) ∧ IsScattered Fq (⊤ : Subfield K) U := by sorry

end ScatCaps.LinearSets
