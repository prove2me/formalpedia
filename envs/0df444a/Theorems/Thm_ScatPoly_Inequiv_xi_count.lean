-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_xi_count
-- name    : ScatPoly.Inequiv.xi_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:52.097771+00:00
-- url     : https://prove2.me/theorems/33b2ec2b-dcd0-4f2b-bdd5-65f78dbf0715
-- title:
--   Proof of Corollary 4.3, p. 18 — ξ_h = 2 or q² + 1, and at most nrξ_h k with U_h ΓL(2, q^n)-equivalent to U_k
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t > 4$, $n = 2t$, $F = \mathbb F_{q^n}$, $H = \{h \in F : h^{q^t+1} = -1\}$, and $U_h = \{(x, \psi_{h,t}(x)) : x \in F\}$. Put
--   $$\xi = \begin{cases} 2, & t \not\equiv 2 \pmod 4,\\ q^2+1, & t \equiv 2 \pmod 4.\end{cases}$$
--   For every $h \in H$:
--
--   1. the number $\xi_h$ of $k \in H$ for which $U_k$ is $\mathrm{GL}(2,q^n)$-equivalent to $U_h$ equals $\xi$ (in particular it does not depend on $h$);
--   2. the number of $k \in H$ for which $U_h$ is $\Gamma\mathrm L(2,q^n)$-equivalent to $U_k$ is at most $n r \xi_h = 2t \cdot r \cdot \xi$.
--
--   These are the class sizes that turn the size $q^t+1$ of $H$ into the lower bounds of Corollary 4.3 and Theorem 5.1; $rn = |\mathrm{Aut}(\mathbb F_{q^n})|$.
--
--   **Formalization Note.** Counts are `Nat.card` of subtypes of $F$. The page's "$\rho$ … $U_{k^\sigma}$" mixes two letters for the same automorphism; this is not modelled, only the two counts are stated.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 18, proof of Corollary 4.3

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem xi_count (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ∈ hSet F q t) :
    Nat.card {k : F // k ∈ hSet F q t ∧ GLEquiv (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t k)) (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t h))} =
        (if t % 4 = 2 then q ^ 2 + 1 else 2) ∧
      Nat.card {k : F // k ∈ hSet F q t ∧ GammaLEquiv (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t h)) (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t k))} ≤
        (2 * t) * r * (if t % 4 = 2 then q ^ 2 + 1 else 2) := by sorry

end ScatPoly.Inequiv
