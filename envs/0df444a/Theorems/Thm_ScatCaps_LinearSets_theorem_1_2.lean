-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_1_2
-- name    : ScatCaps.LinearSets.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:28.264977+00:00
-- url     : https://prove2.me/theorems/0c924ca2-8740-4b39-8e5e-419d5cbdcfbf
-- title:
--   Theorem 1.2, p. 3 — scattered 𝔽_q-linear sets of rank rt/2 exist in PG(r − 1, q^t), t even, in three families of (q, t)
-- statement:
--   Let $\mathbb F_q\subseteq\mathbb F_{q^t}$ be finite fields, $q$ a prime power, $t$ even, and $r\ge2$. Let $V=\mathbb F_{q^t}^{\,r}$, so that $\mathrm{PG}(V,\mathbb F_{q^t})=\mathrm{PG}(r-1,q^t)$. In each of the cases
--
--   1. $q=2$ and $t\ge4$;
--   2. $q\ge2$ and $t\not\equiv0\pmod3$;
--   3. $q\equiv1\pmod3$ and $t\equiv0\pmod3$,
--
--   there is an $\mathbb F_q$-subspace $U\subseteq V$ such that $L_U=\{\langle u\rangle_{\mathbb F_{q^t}}:u\in U\setminus\{0\}\}$ is a scattered $\mathbb F_q$-linear set of
--
--   $$
--   \text{rank}\quad\dim_{\mathbb F_q}U=\frac{rt}{2}.
--   $$
--
--   By Theorem 1.1, $rt/2$ is the largest possible rank of a scattered linear set, so these are maximum scattered linear sets.
--
--   **Formalization Note** The printed theorem gives no range for $r$. The sentence before it says "for each integer $r\ge5$" and the proof (p. 17) says "when $t$ is even and $r\ge5$"; for $r=1$ and $t\ge4$ the statement is false (a single point has weight $t/2>1$). The Lean assumes $r\ge2$, the strongest true reading, covering $r=2$ (line example, p. 2), $r=3$ (§2 and, for $t=2$, the Baer bullet, p. 3) and $r\ge4$ (Theorem 3.1). Rank $rt/2$ is $|U|=q^{rt/2}$, natural division exact because $t$ is even. "$q\ge2$" in case 2 is automatic since $q=|\mathbb F_q|$. Points are spanned over the whole field $\mathbb F_{q^t}$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 3, Theorem 1.2 (range of r from p. 3 and p. 17)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_1_2 (K : Type*) [Field K] [Fintype K]
    (Fq : Subfield K) (q t r : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ t)
    (ht : Even t) (hr : 2 ≤ r)
    (hcase : (q = 2 ∧ 4 ≤ t) ∨ ¬ 3 ∣ t ∨ (q % 3 = 1 ∧ 3 ∣ t)) :
    ∃ U : Set (Fin r → K), IsFqSubspace Fq U ∧
      HasRank Fq U (r * t / 2) ∧ IsScattered Fq (⊤ : Subfield K) U := by sorry

end ScatCaps.LinearSets
